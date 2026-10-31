-- Prove2me | Theorems.Thm_QiFixedDesign_Concentration_lemma_1
-- name    : QiFixedDesign.Concentration.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:00:13.33735+00:00
-- url     : https://prove2.me/theorems/426640a4-4cde-48d7-99ff-2bf49b63c7ad
-- title:
--   Lemma 1 — unrestricted Kantorovich–Rubinstein representation
-- statement:
--   Let $P,Q$ be arbitrary Borel probability measures on a metric space $\Xi$, and let $\mathcal L$ contain all real functions of Lipschitz constant at most one. The printed assertion, read as asserting that its displayed expression is meaningful, says every difference of integrals below is defined and
--   $$W_1(P,Q)=\sup_{f\in\mathcal L}\left(\int f\,dP-\int f\,dQ\right).$$
--   Here $W_1$ is the infimum of transport costs over couplings, not the dual expression. Signed integrals and their differences have extended-real semantics, excluding indeterminate infinity differences through a conclusion, never through a hypothesis restricting the measures or test functions. The unrestricted claim has a missing-definedness defect: a Cauchy law with $f(x)=x$ has neither signed part finite. The source claim remains the target.
--
--   Differences from the source:
--   - encoding: probabilities and possibly infinite transport costs → nonnegative extended real measures and coupling costs; reason: infinite costs stay infinite and finite probabilities have their usual values
--   - reading: an unrestricted supremum of differences of signed integrals without stated definedness → definedness of every displayed difference is asserted in the conclusion together with the equality; reason: a literal meaningfulness reading exposes the Cauchy counterexample without adding finite moments or deleting test functions
--   - encoding: distributions on a metric support → Borel probability measures on an arbitrary metric space; reason: makes the probability and measurable-space conventions explicit without adding completeness or separability
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, Lemma 1, (16), PDF/printed p. 12

import Mathlib
import Definitions.Def_QiFixedDesign_Concentration_IntegralDifference
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

theorem lemma_1 {Ξ : Type*} [MetricSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P Q : ProbabilityMeasure Ξ) :
    (∀ f : Ξ → ℝ, LipschitzWith 1 f →
      IntegralDifferenceDefined (P : Measure Ξ) (Q : Measure Ξ) f) ∧
    (WassersteinLinOpt.Ball.wassersteinDist 1 P Q : EReal) =
      ⨆ (f : Ξ → ℝ) (_ : LipschitzWith 1 f),
        signedIntegral (P : Measure Ξ) f - signedIntegral (Q : Measure Ξ) f := by sorry

end QiFixedDesign.Concentration
