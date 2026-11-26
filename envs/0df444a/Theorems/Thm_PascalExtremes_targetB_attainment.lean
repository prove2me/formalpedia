-- Prove2me | Theorems.Thm_PascalExtremes_targetB_attainment
-- name    : PascalExtremes.targetB_attainment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:00:48.654326+00:00
-- url     : https://prove2.me/theorems/dd777f0e-3fa7-4d2c-b633-2fb77e4fd50a
-- title:
--   Pascal Extremes: target B attainment
-- statement:
--   Target-B attainment at the proposed row, proved by the residue/carry
--   form of Kummer.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L365-L372
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/TargetB.lean#L365-L372

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.targetB_attainment
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    padicValNat p (G (p ^ (3 * a) + 1) (p ^ a + 1)) = a + 1 := by sorry
