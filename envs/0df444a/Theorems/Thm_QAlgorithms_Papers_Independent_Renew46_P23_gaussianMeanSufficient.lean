-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P23_gaussianMeanSufficient
-- name    : QAlgorithms.Papers.Independent.Renew46.P23.gaussianMeanSufficient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:34:55.915509+00:00
-- url     : https://prove2.me/theorems/05e61a42-eae6-41a2-b28b-c7e69384ab3c
-- title:
--   The Gaussian location sample mean is sufficient
-- statement:
--   Fix an integer $n\geq1$ and a standard deviation $\sigma>0$. For each $m\in\mathbb R$, let $P_m=\mathcal N(m,\sigma^2)^{\otimes n}$ be the joint law of $n$ independent real Gaussian observations with mean $m$ and variance $\sigma^2$. Then
--
--   $$T(x)=\frac1n\sum_{i=1}^n x_i$$
--
--   is sufficient for the entire location family $\{P_m:m\in\mathbb R\}$. This is the continuous classical counterpart of the Bernoulli example. The product Gaussian law fixes the intended distribution without using the misprinted expanded exponent on the page.
-- source:
--   Sufficiency in quantum statistical inference. A survey with examples, arXiv:quant-ph/0604091v1, PDF p. 7, Example 4: Gaussian location sample mean

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤

/-- Example 4, PDF p.7: for n ≥ 1 iid normal observations and a fixed positive
standard deviation, the sample mean is sufficient for all real means.
The product Gaussian law, rather than the misprinted expanded exponent,
fixes the intended sign of the location term. -/
theorem gaussianMeanSufficient (n : ℕ) (hn : 1 ≤ n)
    (sigma : ℝ) (hSigma : 0 < sigma) :
    SufficientSigmaAlgebra (gaussianSampleLaw n sigma)
      (MeasurableSpace.comap (fun x : Fin n → ℝ => (∑ i, x i) / (n : ℝ)) (borel ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P23

end
