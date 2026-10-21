-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P23_bernoulliMeanSufficient
-- name    : QAlgorithms.Papers.Independent.Renew46.P23.bernoulliMeanSufficient
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:31:13.959787+00:00
-- url     : https://prove2.me/theorems/31eeaf32-ce9d-4c65-8807-15cc11a280c6
-- title:
--   The Bernoulli sample mean is sufficient
-- statement:
--   Let $n\geq1$. For each $p\in[0,1]$, let $P_p$ be the product law of $n$ independent Bernoulli observations $x_i\in\{0,1\}$, with success probability $p$. Then the empirical mean
--
--   $$T(x)=\frac1n\sum_{i=1}^n x_i$$
--
--   is sufficient for the entire family $\{P_p:p\in[0,1]\}$. Thus, for each measurable event, a single conditional-probability version given $T$ works under every $P_p$, including the endpoint distributions. This gives the classical sample-mean example of lossless statistical compression.
-- source:
--   Sufficiency in quantum statistical inference. A survey with examples, arXiv:quant-ph/0604091v1, PDF p. 2, Introduction: Bernoulli sample mean is sufficient

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

/-- Introduction, PDF p.2: the empirical mean is sufficient for the complete
Bernoulli parameter family [0,1]. One conditional version works for every p. -/
theorem bernoulliMeanSufficient (n : ℕ) (hn : 1 ≤ n) :
    SufficientSigmaAlgebra (bernoulliSampleLaw n)
      (MeasurableSpace.comap
        (fun x : Fin n → Bool => (∑ i, if x i then (1 : ℝ) else 0) / (n : ℝ))
        (borel ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P23

end
