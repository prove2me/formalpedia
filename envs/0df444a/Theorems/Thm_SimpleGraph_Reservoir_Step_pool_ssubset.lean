-- Prove2me | Theorems.Thm_SimpleGraph_Reservoir_Step_pool_ssubset
-- name    : SimpleGraph.Reservoir.Step.pool_ssubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:24.557373+00:00
-- url     : https://prove2.me/theorems/87e7910a-24a4-4517-9192-a96fdea3893f
-- title:
--   Step: pool ssubset
-- statement:
--   A step strictly shrinks the pool.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L193-L196
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Reservoir.lean#L193-L196

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

theorem SimpleGraph.Reservoir.Step.pool_ssubset {R R' : G.Reservoir} (h : Step R R') : R'.pool ⊂ R.pool := by sorry
