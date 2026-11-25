-- Prove2me | Theorems.Thm_SmallRatio_dedekindSum_eq_Asum
-- name    : SmallRatio.dedekindSum_eq_Asum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:10.124075+00:00
-- url     : https://prove2.me/theorems/c644cb1f-1134-432f-9be3-0ead800545c0
-- title:
--   Small Ratio: dedekind Sum eq Asum
-- statement:
--   The Small Ratio construction uses the dedekind Sum eq Asum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L77-L127
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L77-L127

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.dedekindSum_eq_Asum (h k : ℕ) (hk : 0 < k) (hc : Nat.Coprime h k) :
    dedekindSum h k = (Asum h k : ℚ) / (k : ℚ) ^ 2 - ((k : ℚ) - 1) / 4 := by sorry
