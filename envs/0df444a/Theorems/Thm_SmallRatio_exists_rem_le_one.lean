-- Prove2me | Theorems.Thm_SmallRatio_exists_rem_le_one
-- name    : SmallRatio.exists_rem_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:19:22.297881+00:00
-- url     : https://prove2.me/theorems/1c78ed6d-7661-5f0d-9c98-41056ad0af72
-- title:
--   Small Ratio: exists rem le one
-- statement:
--   The Small Ratio construction uses the exists rem le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L52-L57
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L52-L57

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}

theorem SmallRatio.exists_rem_le_one : ∃ j ≤ h + 1, rem k h j ≤ 1 := by sorry
