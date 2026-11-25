-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_Reaches_card_add_card_le
-- name    : SimpleGraph.Reservoir.Reaches.card_add_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:16.285967+00:00
-- url     : https://prove2.me/theorems/6d10b8cd-60a5-4bf3-95cd-bbd4625c5325
-- title:
--   Reaches: card add card le
-- statement:
--   Along a run of pivots, the spine grows by the number of steps while the pool shrinks by at
--   least as much: `#spine + #pool` never increases.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L214-L221
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L214-L221

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

theorem SimpleGraph.Reservoir.Reaches.card_add_card_le {R R' : G.Reservoir} (h : Reaches R R') :
    #R'.spine + #R'.pool ≤ #R.spine + #R.pool := by sorry
