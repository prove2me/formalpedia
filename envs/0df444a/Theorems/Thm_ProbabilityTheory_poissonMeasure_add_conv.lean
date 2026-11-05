-- Prove2me | Theorems.Thm_ProbabilityTheory_poissonMeasure_add_conv
-- name    : ProbabilityTheory.poissonMeasure_add_conv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:54:28.189416+00:00
-- url     : https://prove2.me/theorems/07dd3131-6cf4-4370-9e54-ffaa2948a2f4
-- title:
--   Convolution law for independent Poisson counts (LeanLevy source)
-- statement:
--   The sum of two independent Poisson counts with respective intensities a and b has the Poisson law of intensity a+b. The exact LeanLevy source delegates directly to the pinned Mathlib convolution theorem.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/Probability/Poisson.lean original theorem around lines 238-242.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Group.Convolution

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

theorem ProbabilityTheory.poissonMeasure_add_conv (a b : ℝ≥0) :
    ((poissonMeasure a).prod (poissonMeasure b)).map (fun p : ℕ × ℕ => p.1 + p.2) =
    poissonMeasure (a + b) := by sorry
