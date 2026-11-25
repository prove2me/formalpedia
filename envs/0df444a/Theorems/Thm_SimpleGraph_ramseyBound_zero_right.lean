-- Prove2me | Theorems.Thm_SimpleGraph_ramseyBound_zero_right
-- name    : SimpleGraph.ramseyBound_zero_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:49.317911+00:00
-- url     : https://prove2.me/theorems/25b7c1d4-5965-5db1-853e-1f892fc820f7
-- title:
--   Simple Graph: ramsey Bound zero right
-- statement:
--   Every graph, on any number `n` of vertices, has an independent `0`-set.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L104-L104
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L104-L104

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

theorem SimpleGraph.ramseyBound_zero_right (n r : ℕ) : RamseyBound n r 0 := by sorry
