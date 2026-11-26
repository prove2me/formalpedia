-- Prove2me | Theorems.Thm_PascalExtremes_coprime_pow_two_a_m
-- name    : PascalExtremes.coprime_pow_two_a_m
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:28.391535+00:00
-- url     : https://prove2.me/theorems/f1e044a4-ff9c-4b00-ab69-772bfd8e967e
-- title:
--   Pascal Extremes: coprime pow two a m
-- statement:
--   The Pascal Extremes construction uses the coprime pow two a m property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L79-L83
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L79-L83

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.coprime_pow_two_a_m
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    Nat.Coprime (p ^ (2 * a)) (p ^ a + 1) := by sorry
