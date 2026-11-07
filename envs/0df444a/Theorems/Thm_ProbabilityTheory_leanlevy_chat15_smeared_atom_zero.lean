-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_smeared_atom_zero
-- name    : ProbabilityTheory.leanlevy_chat15_smeared_atom_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:33:32.470203+00:00
-- url     : https://prove2.me/theorems/6c2200b5-907e-496a-b81c-bd911fe4d7d0
-- title:
--   Dirac atom of smeared measure under a zero-mass origin
-- statement:
--   Adding a density against a measure with no atom at zero does not alter the coefficient of a Dirac atom at zero.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 113-124.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat15_smeared_atom_zero (a : ℝ≥0∞) {ν : MeasureTheory.Measure ℝ} (hν0 : ν {0} = 0) (f : ℝ → ℝ≥0∞) : (a • MeasureTheory.Measure.dirac (0 : ℝ) + ν.withDensity f) {0} = a := by sorry
