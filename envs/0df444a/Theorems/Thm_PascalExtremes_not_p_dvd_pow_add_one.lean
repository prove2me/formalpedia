-- Prove2me | Theorems.Thm_PascalExtremes_not_p_dvd_pow_add_one
-- name    : PascalExtremes.not_p_dvd_pow_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:17.069333+00:00
-- url     : https://prove2.me/theorems/fe0c657e-6db8-50b4-8404-589fbd9e4d29
-- title:
--   Pascal Extremes: not p dvd pow add one
-- statement:
--   The Pascal Extremes construction uses the not p dvd pow add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L69-L77
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L69-L77

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.not_p_dvd_pow_add_one
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ¬ p ∣ p ^ a + 1 := by sorry
