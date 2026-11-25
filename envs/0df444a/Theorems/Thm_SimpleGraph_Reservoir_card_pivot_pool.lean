-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_card_pivot_pool
-- name    : SimpleGraph.Reservoir.card_pivot_pool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:13.689908+00:00
-- url     : https://prove2.me/theorems/b8e1cc9e-84e3-4ae1-b855-ee769b695b48
-- title:
--   Reservoir: card pivot pool
-- statement:
--   **Loss of a pivot.** Pivoting at `v` loses exactly the pool vertices not adjacent to `v`
--   (including `v` itself).
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L168-L169
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L168-L169

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

theorem SimpleGraph.Reservoir.card_pivot_pool : #(R.pivot v hv).pool + #{w ∈ R.pool | ¬G.Adj v w} = #R.pool := by sorry
