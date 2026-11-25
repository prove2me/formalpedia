-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_Step_card_spine
-- name    : SimpleGraph.Reservoir.Step.card_spine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:27:18.468221+00:00
-- url     : https://prove2.me/theorems/54ebc48f-7bc3-4f1c-86b0-922e7eba42b5
-- title:
--   Step: card spine
-- statement:
--   A step grows the spine by one.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L188-L190
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L188-L190

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
variable [DecidableEq V] [DecidableRel G.Adj]

theorem SimpleGraph.Reservoir.Step.card_spine {R R' : G.Reservoir} (h : Step R R') : #R'.spine = #R.spine + 1 := by sorry
