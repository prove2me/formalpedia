-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_countableCommonNullSubfamily
-- name    : QAlgorithms.Papers.Independent.Next46.P43.countableCommonNullSubfamily
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:37:22.357071+00:00
-- url     : https://prove2.me/theorems/547cf4e9-a15b-4ede-a5a4-7ed8dd305d77
-- title:
--   Lemma 1: countable common-null-set subfamily
-- statement:
--   Let $(X,\mathcal A)$ be a measurable space and let $(P_\theta)_{\theta\in\Theta}$ be a nonempty family of probability measures. Suppose $\mu$ is sigma-finite and $P_\theta\ll\mu$ for every $\theta$. There is a sequence of indices $s:\mathbb N\to\Theta$ such that, for every $A\in\mathcal A$,
--
--   $$
--   (\forall\theta,\ P_\theta(A)=0)\quad\Longleftrightarrow\quad(\forall n,\ P_{s(n)}(A)=0).
--   $$
--
--   The sequence may repeat indices, so a finite selected family is included. It identifies the common null sets using countably many members.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 4, Lemma 1: countable common-null-set subfamily

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Lemma 1, PDF p.4. The classical probability family is nonempty and has a
sigma-finite dominating measure. A sequence may repeat selected members, so
finite subfamilies are included. Null equivalence is for every measurable set. -/
theorem countableCommonNullSubfamily
    {X Theta : Type*} [MeasurableSpace X] [Nonempty Theta]
    (P : Theta → Measure X) (hProb : ∀ theta, IsProbabilityMeasure (P theta))
    (mu : Measure X) [SigmaFinite mu]
    (hDom : ∀ theta, P theta ≪ mu) :
    ∃ selected : ℕ → Theta, ∀ A, MeasurableSet A →
      ((∀ theta, P theta A = 0) ↔ ∀ n, P (selected n) A = 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
