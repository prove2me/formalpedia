-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaA_3
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaA_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:47:22.237696+00:00
-- url     : https://prove2.me/theorems/c8aecfc5-4ff8-4beb-8adc-68572522e177
-- title:
--   Testing-entropy primal and dual values
-- statement:
--   Let $\rho,\sigma\ge0$ on a nonzero finite-dimensional system and $0\le\epsilon\le\operatorname{tr}\rho$. For positive $\epsilon$, let $v_H^\epsilon$ be the infimum of $\operatorname{tr}(Q\sigma)/\epsilon$ over $0\le Q\le1$ with $\operatorname{tr}(Q\rho)\ge\epsilon$. Then
--
--   $$v_H^\epsilon=\sup_{\mu\ge0,\ Y\ge0,\ \mu(\rho-Y)\le\sigma}\mu\left(1-\frac{\operatorname{tr}Y}{\epsilon}\right)=2^{-D_H^\epsilon(\rho\|\sigma)}.$$
--
--   At $\epsilon=0$, both sides denote their continuous right extensions, rather than division by zero. The equality is stated for the extended nonnegative optimization values, including zero and infinity. This is the dual characterization used in the testing-entropy estimate.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 19, Lemma A.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma A.3, Eq.146 (PDF pp.19–20): equality of primal and dual values,
including the continuous zero-epsilon endpoint. Endpoint values are computed
from positive-epsilon optimizations; no 0/0 logarithm is used. -/
theorem lemmaA_3 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Op I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hbound : epsilon ≤ rho.trace.re) :
    endpointTestingValue epsilon rho sigma = endpointDualValue epsilon rho sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
