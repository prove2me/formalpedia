-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_lintegral_id_poissonMeasure
-- name    : ProbabilityTheory.leanlevy_lintegral_id_poissonMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:22:24.447545+00:00
-- url     : https://prove2.me/theorems/42ca224d-138a-4b37-8332-378f2405c41b
-- title:
--   ENNReal mean of a Poisson law (Campbell helper)
-- statement:
--   The nonnegative extended-real Lebesgue integral of the natural-number identity against a Poisson probability measure of parameter r equals r. This is the source-exact content of the private Poisson mean lemma used in LeanLevy Campbell's formula.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/RandomMeasure/PoissonRandomMeasure.lean lines 129–146, private lintegral_id_poissonMeasure promoted under a distinct helper name.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open scoped ENNReal NNReal Nat
open MeasureTheory Real ProbabilityTheory

theorem ProbabilityTheory.leanlevy_lintegral_id_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(poissonMeasure r) = (r : ℝ≥0∞) := by sorry
