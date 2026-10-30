-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_lemma2
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.lemma2
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:26:54.053012+00:00
-- url     : https://prove2.me/theorems/453b0d6d-9866-4337-be76-291b9132bfa6
-- title:
--   Lemma 2: conditional misclassification identity
-- statement:
--   Let $\mu_0,\mu_1$ be the conditional probability laws of a measurable exact model output $X$ in the two classes, sampled with equal prior probabilities. Suppose $X=c$ almost surely in class 1 and $X\in[b_1,b_2]$ almost surely in class 0. Set $p=\mu_0\{X=c\}$. Then
--
--   $$\Pr(0\mid X=c)=\frac{p}{1+p}.$$
--
--   The posterior is defined by the actual atom probabilities under the equal-prior mixture. Its conditioning event has mixture probability at least $1/2$, so no conditional density or null-event convention is used.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 26, Lemma 2: conditional misclassification identity

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.26–27, Lemma 2, Eq.(E2): the omitted short-statement premise
that every class-1 output is c is retained from Eq.(E1). -/
theorem lemma2 {Omega : Type*} [MeasurableSpace Omega]
    (mu0 mu1 : Measure Omega) [IsProbabilityMeasure mu0] [IsProbabilityMeasure mu1]
    (X : Omega → ℝ) (hX : Measurable X) (c b1 b2 : ℝ)
    (hclass1 : ∀ᵐ w ∂mu1, X w = c)
    (hclass0 : ∀ᵐ w ∂mu0, X w ∈ Set.Icc b1 b2) :
    posteriorAt mu0 mu1 X c =
      (mu0 {w | X w = c}).toReal / (1 + (mu0 {w | X w = c}).toReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
