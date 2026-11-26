-- Prove2me | Theorems.Thm_PascalExtremes_mul_q0_eq_pow_three_add_one
-- name    : PascalExtremes.mul_q0_eq_pow_three_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:13.26918+00:00
-- url     : https://prove2.me/theorems/8b23fbe4-e636-592c-95d4-874f6c453245
-- title:
--   Pascal Extremes: mul q0 eq pow three add one
-- statement:
--   The Pascal Extremes construction uses the mul q0 eq pow three add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L38-L67
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L38-L67

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.mul_q0_eq_pow_three_add_one
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (p ^ a + 1) * q0 p a = p ^ (3 * a) + 1 := by sorry
