-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_Reaches_pool_subset
-- name    : SimpleGraph.Reservoir.Reaches.pool_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:13.724511+00:00
-- url     : https://prove2.me/theorems/986cd5ea-5fac-45a2-8d20-c8a7e9adba8d
-- title:
--   Reaches: pool subset
-- statement:
--   Pools only shrink along a run of steps.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L207-L210
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L207-L210

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

theorem SimpleGraph.Reservoir.Reaches.pool_subset {R R' : G.Reservoir} (h : Reaches R R') : R'.pool ⊆ R.pool := by sorry
