-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_Reaches_spine_subset
-- name    : SimpleGraph.Reservoir.Reaches.spine_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:11.442851+00:00
-- url     : https://prove2.me/theorems/83de8dfc-d93a-4322-9a9f-25faad661a37
-- title:
--   Reaches: spine subset
-- statement:
--   Spines only grow along a run of steps.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L199-L204
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L199-L204

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

theorem SimpleGraph.Reservoir.Reaches.spine_subset {R R' : G.Reservoir} (h : Reaches R R') : R.spine ⊆ R'.spine := by sorry
