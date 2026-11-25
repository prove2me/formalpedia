-- Prove2me | Theorems.Thm_SimpleGraph_ramseyBound_comm
-- name    : SimpleGraph.ramseyBound_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:46.548338+00:00
-- url     : https://prove2.me/theorems/b84440f8-b2a9-54a1-b43f-a1ecd6287ae7
-- title:
--   Simple Graph: ramsey Bound comm
-- statement:
--   `RamseyBound n r s ↔ RamseyBound n s r`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L98-L98
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L98-L98

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

theorem SimpleGraph.ramseyBound_comm : RamseyBound n r s ↔ RamseyBound n s r := by sorry
