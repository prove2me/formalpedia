-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_smeared_restrict_compl
-- name    : ProbabilityTheory.leanlevy_chat15_smeared_restrict_compl
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:34:31.174907+00:00
-- url     : https://prove2.me/theorems/564e3a81-5a35-40a1-8a5c-d1860aea8196
-- title:
--   Smeared measure restriction removes only the Dirac atom
-- statement:
--   A Dirac atom at zero vanishes under restriction to the nonzero line while a density over a base measure with zero singleton mass is unchanged.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 432-445.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat15_smeared_restrict_compl (a : ℝ≥0∞) {ν : MeasureTheory.Measure ℝ} (hν0 : ν {0} = 0) (f : ℝ → ℝ≥0∞) : (a • MeasureTheory.Measure.dirac (0 : ℝ) + ν.withDensity f).restrict ({(0 : ℝ)}ᶜ) = ν.withDensity f := by sorry
