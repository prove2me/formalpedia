-- Prove2me | Theorems.Thm_SmallRatio_sawtooth_natCast_div
-- name    : SmallRatio.sawtooth_natCast_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:15:05.576146+00:00
-- url     : https://prove2.me/theorems/3af69922-9a0e-422f-83cd-97a079db478e
-- title:
--   Small Ratio: sawtooth nat Cast div
-- statement:
--   The Small Ratio construction uses the sawtooth nat Cast div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L41-L49
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Reciprocity.lean#L41-L49

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset

theorem SmallRatio.sawtooth_natCast_div (n k : ℕ) (hk : 0 < k) (hn : ¬ k ∣ n) :
    sawtooth ((n : ℚ) / k) = ((n % k : ℕ) : ℚ) / k - 1 / 2 := by sorry
