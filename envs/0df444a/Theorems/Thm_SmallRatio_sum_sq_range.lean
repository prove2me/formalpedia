-- Prove2me | Theorems.Thm_SmallRatio_sum_sq_range
-- name    : SmallRatio.sum_sq_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:19.708152+00:00
-- url     : https://prove2.me/theorems/8af9ef30-bcfa-4afe-a86d-f80731c07ab5
-- title:
--   Small Ratio: sum sq range
-- statement:
--   The Small Ratio construction uses the sum sq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L204-L207
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L204-L207

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.sum_sq_range (m : ℕ) : 6 * ∑ r ∈ range m, (r : ℚ) ^ 2 = ((m : ℚ) - 1) * m * (2 * m - 1) := by sorry
