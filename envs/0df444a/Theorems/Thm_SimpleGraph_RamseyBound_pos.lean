-- Prove2me | Theorems.Thm_SimpleGraph_RamseyBound_pos
-- name    : SimpleGraph.RamseyBound.pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:51.860496+00:00
-- url     : https://prove2.me/theorems/57114e1d-76c4-5f88-bca9-c39763e37da6
-- title:
--   Ramsey Bound: pos
-- statement:
--   A Ramsey bound for positive `r` and `s` is positive: the graph with no vertices has neither a
--   `1`-clique nor an independent `1`-set.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L116-L122
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/RamseyBound.lean#L116-L122

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

theorem SimpleGraph.RamseyBound.pos (h : RamseyBound n r s) (hr : 0 < r) (hs : 0 < s) : 0 < n := by sorry
