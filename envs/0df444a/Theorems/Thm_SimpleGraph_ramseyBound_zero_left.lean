-- Prove2me | Theorems.Thm_SimpleGraph_ramseyBound_zero_left
-- name    : SimpleGraph.ramseyBound_zero_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:40.522589+00:00
-- url     : https://prove2.me/theorems/bbba4933-c179-4cb5-8548-17b29cc55cc5
-- title:
--   Simple Graph: ramsey Bound zero left
-- statement:
--   Every graph contains the empty clique.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L101-L101
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L101-L101

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

theorem SimpleGraph.ramseyBound_zero_left (n s : ℕ) : RamseyBound n 0 s := by sorry
