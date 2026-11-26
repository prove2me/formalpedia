-- Prove2me | Theorems.Thm_PascalExtremes_q0_row_admissible
-- name    : PascalExtremes.q0_row_admissible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:51.432981+00:00
-- url     : https://prove2.me/theorems/2ee03237-d084-491e-88fa-9a9a606eef08
-- title:
--   Pascal Extremes: q0 row admissible
-- statement:
--   The Pascal Extremes construction uses the q0 row admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L85-L98
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L85-L98

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.q0_row_admissible
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    AdmissibleRow (p ^ a + 1) (p ^ (3 * a) + 1) := by sorry
