-- Prove2me | Theorems.Thm_SimpleGraph_RamseyBound_mono
-- name    : SimpleGraph.RamseyBound.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:44.464389+00:00
-- url     : https://prove2.me/theorems/90b72b5a-ffe3-53a1-94c9-60be96c549bd
-- title:
--   Ramsey Bound: mono
-- statement:
--   More vertices: a Ramsey bound `n` for `(r, s)` gives every `m ≥ n`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L88-L91
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L88-L91

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

theorem SimpleGraph.RamseyBound.mono (h : RamseyBound n r s) (hnm : n ≤ m) : RamseyBound m r s := by sorry
