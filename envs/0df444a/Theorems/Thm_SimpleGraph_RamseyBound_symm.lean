-- Prove2me | Theorems.Thm_SimpleGraph_RamseyBound_symm
-- name    : SimpleGraph.RamseyBound.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:36.918593+00:00
-- url     : https://prove2.me/theorems/60f2e411-2d3c-4285-9d49-6189df35dbed
-- title:
--   Ramsey Bound: symm
-- statement:
--   Ramsey bounds are symmetric in the two colours.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L94-L95
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L94-L95

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

theorem SimpleGraph.RamseyBound.symm (h : RamseyBound n r s) : RamseyBound n s r := by sorry
