-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_pivot_pool_eq_inter
-- name    : SimpleGraph.Reservoir.pivot_pool_eq_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:10.096728+00:00
-- url     : https://prove2.me/theorems/ad605fc1-64cd-5760-bba2-6c3e8edec162
-- title:
--   Reservoir: pivot pool eq inter
-- statement:
--   The pool after pivoting at `v` is the neighbourhood of `v` inside the pool.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L161-L164
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L161-L164

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}
variable (R : G.Reservoir)
variable [DecidableRel G.Adj] [DecidableEq V]
variable {v : V} (hv : v ∈ R.pool)

theorem SimpleGraph.Reservoir.pivot_pool_eq_inter [Fintype (G.neighborSet v)] :
    (R.pivot v hv).pool = R.pool ∩ G.neighborFinset v := by sorry
