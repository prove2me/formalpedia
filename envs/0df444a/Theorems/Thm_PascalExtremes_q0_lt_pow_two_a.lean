-- Prove2me | Theorems.Thm_PascalExtremes_q0_lt_pow_two_a
-- name    : PascalExtremes.q0_lt_pow_two_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:34.396361+00:00
-- url     : https://prove2.me/theorems/1628bcc5-3539-4540-877d-b655433dcd9c
-- title:
--   Pascal Extremes: q0 lt pow two a
-- statement:
--   The Pascal Extremes construction uses the q0 lt pow two a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L24-L36
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L24-L36

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.q0_lt_pow_two_a {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    q0 p a < p ^ (2 * a) := by sorry
