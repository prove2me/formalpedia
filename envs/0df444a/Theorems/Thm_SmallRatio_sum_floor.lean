-- Prove2me | Theorems.Thm_SmallRatio_sum_floor
-- name    : SmallRatio.sum_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:20.134803+00:00
-- url     : https://prove2.me/theorems/0c6512ed-c614-4bf9-b93b-995ab7464fc8
-- title:
--   Small Ratio: sum floor
-- statement:
--   `∑_{j<h} ⌊kj/h⌋ = (h-1)(k-1)/2`.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L186-L202
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L186-L202

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.sum_floor (h k : ℕ) (hh : 0 < h) (hc : Nat.Coprime h k) :
    2 * ∑ j ∈ range h, ((k * j / h : ℕ) : ℤ) = ((h : ℤ) - 1) * ((k : ℤ) - 1) := by sorry
