-- Prove2me | Theorems.Thm_SimpleGraph_ChromaticPolynomial_eval
-- name    : SimpleGraph.ChromaticPolynomial_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:58.475836+00:00
-- url     : https://prove2.me/theorems/2e972a42-96b5-4e2b-b942-5c8d0cf41978
-- title:
--   Simple Graph: Chromatic Polynomial eval
-- statement:
--   The chromatic polynomial of a graph G evaluated at a integer n is the number of proper
--     colorings of the graph with n colors.
--
--   Source: https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/ChromaticPolynomial/ChromaticPolynomial.lean#L224-L288
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/ChromaticPolynomial/ChromaticPolynomial.lean#L224-L288

module
public import Definitions.Def_ChromaticPolynomial_SpanningSubgraph
public import Definitions.Def_ChromaticPolynomial_ConstantOnConnectedComponents
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Set
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
set_option autoImplicit true
@[expose] public section
public section
universe u
open SimpleGraph
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
open Classical
variable (R: Type*) [CommRing R] [CharZero R] [NoZeroDivisors R]
variable (α : Type*) [Fintype α]
variable (e : Sym2 V)
open Finset

theorem SimpleGraph.ChromaticPolynomial_eval (α : Type*) [Fintype α] :
  (G.ChromaticPolynomial R).eval (Fintype.card α : R) = Fintype.card (G.Coloring α) := by sorry
