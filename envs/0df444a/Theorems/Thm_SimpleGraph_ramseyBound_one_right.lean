-- Prove2me | Theorems.Thm_SimpleGraph_ramseyBound_one_right
-- name    : SimpleGraph.ramseyBound_one_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:52.198401+00:00
-- url     : https://prove2.me/theorems/27daf8e0-0069-45e9-90d4-b23f861e48e2
-- title:
--   Simple Graph: ramsey Bound one right
-- statement:
--   For `n ≥ 1`, every graph on `n` vertices has an independent `1`-set.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L111-L112
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L111-L112

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}

theorem SimpleGraph.ramseyBound_one_right (hn : 0 < n) (r : ℕ) : RamseyBound n r 1 := by sorry
