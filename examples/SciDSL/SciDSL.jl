module SciDSL
using SemanticModels
using MacroTools
using Catlab
using Catlab.WiringDiagrams
import Catlab.WiringDiagrams: WiringDiagram
using Catlab.Doctrines
import Catlab.Graphics: to_graphviz
import Catlab.Graphics.Graphviz: run_graphviz
using ModelingToolkit
import ModelingToolkit: Operation

abstract type Framework end

struct WireFramework{T,U,D} <: Framework
    name::Symbol
    objects::T
    morphisms::U
    diagrams::Vector{D}
end

name(wf::WireFramework) = wf.name
objects(wf::WireFramework) = wf.objects
morphisms(wf::WireFramework) = wf.morphisms
diagrams(wf::WireFramework) = wf.diagrams

struct Value{F,T,Ob}
    framework::F
    value::T
    object::Ob
end

macro framework(name, ex)
    println("Creating Framework: $name")
    objs = Dict{Symbol, Catlab.Doctrines.FreeSymmetricMonoidalCategory.Ob{:generator}}()
    homs = Dict{Any, Catlab.Doctrines.FreeSymmetricMonoidalCategory.Hom{:generator}}()
    extract_entities(objs, homs, ex)
    @show objs
    @show homs
    q = quote WireFramework($(QuoteNode(name)), $objs, $homs, []) end
    return q
end

macro obj(name, typ)
    println("Creating Obj: $name::$typ")
    objectinst = :(Ob(FreeSymmetricMonoidalCategory, $(QuoteNode(name))))
    q = quote
        $name = $objectinst
    end
    # @show q
    return q
end


macro hom(var, name, pex)
    println("Creating Hom: $var, $name, $pex")
    # p = eval(pex)
    # p1 = p.args[2]
    # p2 = p.args[3]
    # dom = foldl(⊗, map(p1) do x
    # cod = foldl(⊗, p2)
    # q = quote
    #     Hom($(QuoteNode(name)), $dom, $cod)
    # end
    # @show q
    # return q
end

macro eqn(ex)
    println("Creating Eqn: $ex")
    return ex
end

head(x) = isa(x, Expr) ? x.head : nothing

function extract_entities(objs, morphs, ex)
    MacroTools.postwalk(ex) do x
        if isa(x, Symbol)
            return x
        end
        if isa(x, LineNumberNode)
            return x
        end
        if isa(x, QuoteNode)
            return x
        end
        if x.head == :macrocall
            # @show x.args[1]
            if x.args[1] == Symbol("@obj")
                A = eval(x)
                # @show typeof(A)
                objs[Symbol(A)] = A
            end
            if x.args[1] == Symbol("@hom")
                p = x.args[5]
                p1 = p.args[2].args
                p2 = p.args[3].args
                dom = foldl(⊗, map(p1) do x; objs[x] end)
                cod = foldl(⊗, map(p2) do x; objs[x] end)
                name = x.args[4]
                f = Hom(name, dom, cod)
                # @show typeof(f)
                morphs[eval(x.args[3])] = f
            end
            if x.args[1] == Symbol("@eqn")
                warn("Equations not yet supported")
            end
        end
        return x
end
end


struct Tree{D}
    body::Expr
    lookup::D
end

function Tree(sig::Expr, body::Expr)
    lookup = Dict{Symbol, Union{Symbol,Expr}}()
    for arg in sig.args[2:end]
        lookup[arg.args[1]] = arg.args[2]
    end
    #TODO: consider using Vector{Union{Symbol, Expr}} to track changes multiple assignments to same var
    newbody = MacroTools.postwalk(body) do x
        if head(x) == :(=)
            var, val = x.args[1], x.args[2]
            lookup[var] = val
        end
        if head(x) == :call
            x = MacroTools.postwalk(x) do y
                if y in keys(lookup)
                    return lookup[y]
                end
                return y
            end
        end
        if head(x) == :return
            return map(x.args) do y
                lookup[y]
            end
        end
        return x
    end
    ex = newbody.args[end]
    if length(ex) == 1
        return Tree(ex[1], lookup)
    end
    return Tree(:(vec($(ex...))), lookup)
end

function WiringDiagram(frm::Framework, t::Tree)
    d = MacroTools.postwalk(t.body) do x
        if head(x) == :vec
            println("vec")
            return foldl(otimes, x.args[2:end])
        end
        if head(x) == :call
            f = x.args[1]
            return compose(foldl(otimes, x.args[2:end]), f)
        end
        if isa(x, Symbol)
            if x in keys(objects(frm))
                println("found $x as an object")
                return WiringDiagram(Ports([objects(frm)[x]]), Ports([objects(frm)[x]]))
            end
            if x in keys(morphisms(frm))
                println("found $x as an morphism")
                return WiringDiagram(morphisms(frm)[x])
            end
            println("did not find $x as an object/morphism")
            return x
        end
        return x
    end
end

function WiringDiagram(frm::Framework, typedict::Dict, t::Operation)
    @show t
    @show fname = nameof(t.op)
    if length(t.args) == 0
        println("Base Case")
        x = typedict[Symbol(t.op)]
        return WiringDiagram(Ports([objects(frm)[x]]), Ports([objects(frm)[x]]))
    end
    println("Recursive Case")
    f = morphisms(frm)[fname]
    args = map(t.args) do x
        WiringDiagram(frm, typedict, x)
    end
    return compose(foldl(otimes, args), WiringDiagram(f))
    # return t
end

striptypes(args) = map(args[2:end]) do arg
    arg.args[1]
end

funcdef(name::Symbol, argnames, body::Expr) = begin
    sig = :($name($(argnames...)))
    return :($sig = $body)
end

macro wiring(ctx, sig, body)
    t = Tree(sig, body)
    c = eval(ctx)
    d = WiringDiagram(c, t)
    argnames = striptypes(sig.args)
    fname = sig.args[1]
    push!(c.diagrams, d)
    return funcdef(fname, argnames, body)
end

using ModelingToolkit

macro wiring_toolkit(ctx, sig, body)
    argnames = striptypes(sig.args)
    typedict = Dict(a.args[1]=>a.args[2] for a in sig.args[2:end])
    fname = sig.args[1]
    f = funcdef(fname, argnames, body)
    vars =:(@variables $(argnames...))
    q = quote
        $f
        $vars
        result = $fname($(argnames...))
        WiringDiagram($ctx, $typedict, result)
    end
    return q
end

create(f::Framework, v, T) = Value(f, v, T)

frm = @framework Foo begin
    @obj A Int
    @obj B Float64

    @hom :f :foo [A] => [B]
    @hom :g :goo [B] => [A]
    @hom :h :hoo [A, A] => [B]
end

f(x::Int) = sqrt(x)
g(x::Float64) = floor(Int, x)
h(x::Int,y::Int) = x - y*y

# f.diagrams[end] = compose(f.diagrams[end], f)
# A, B = frm.objects[:A], frm.objects[:B]
# f(x::Value) =  Value(x.framework, f(x.value), B)
# g(x::Value) =  Value(x.framework, g(x.value), A)
# h(x::Value, y::Value) =  Value(x.framework, h(x.value, y.value), B)

@register f(x)
@register g(x)
@register h(x,y)

# function prog(frm)
#     x = create(frm, 2, frm.objects[:A])
#     y = g(f(x))
#     z = h(x, y)
# end

@wiring frm prog(x::A) begin
    y = g(f(x))
    z = h(x, y)
    return z
end

@show frm.diagrams[1]

operation = @wiring_toolkit frm prog(x::A) begin
    y = g(f(x))
    z = h(x, y)
    return z
end
@show operation
# TODO: debug diagram
# @code_lowered prog(frm)

function writesvg(f::Union{IO,AbstractString}, d::WiringDiagram)
    write(f, ( (to_graphviz(d, labels=true)) |> g->@show run_graphviz(g, format="svg") )
          )
end

# TODO: debug display
writesvg("dsl1.svg", frm.diagrams[1])
end

epi = @framework Epi begin
    @obj P Person

    @hom :f :spontaneous  [P] => [P]
    @hom :g :interaction  [P, P] => [P, P]
    @hom :h :triple       [P, P, P] => [P, P, P]
end

@wiring epi SIRS(s::P, i::P) begin
    i,i = g(s,i)
    r = f(i)
    d = f(i)
    s = f(r)
end


epi = @framework Epi begin
    @obj S Person
    @obj I Person
    @obj R Person
    @obj D Person

    @hom :f :infect  [S, I] => [I I]
    @hom :g :recover [I] => [R]
    @hom :j :wane    [R] => [S]
    @hom :h :die     [I] => [D]
end

@wiring epi SIRS(s::S, i::I) begin
    i1, i2 = infect(s,i)
    r, d   = recover(i1), die(i2)
    w      = wane(r)
    return w, d
end # returns a morphism from S⊗I → S⊗D
