-- Prove2me | Theorems.Thm_SimpleGraph_cliqueCountIn_one
-- name    : SimpleGraph.cliqueCountIn_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:43.543897+00:00
-- url     : https://prove2.me/theorems/a5b2dc92-660b-42d8-927a-90bf7528e7ab
-- title:
--   Simple Graph: clique Count In one
-- statement:
--   The `1`-cliques inside `S` are its vertices.
--
--   Source: https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L191-L194
-- source:
--   https://github.com/Egly443/lean-goodman-supersaturation/blob/6c32aa44315c4627ceff231bd15c8d48fa4bf2e7/GoodmanSupersaturation/Supersaturation.lean#L191-L194

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem SimpleGraph.cliqueCountIn_one (S : Finset V) : G.cliqueCountIn S 1 = #S := by sorry
