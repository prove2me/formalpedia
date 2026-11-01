-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P69_equalNoiseChainComparison
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P69.equalNoiseChainComparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:38:11.870129+00:00
-- url     : https://prove2.me/theorems/8bfd237f-5674-4d99-a45a-7279574e7fd5
-- title:
--   Equal-noise additive chain comparison identity
-- statement:
--   Let $N\ge0$ be an integer and let $\xi>0$ be a total additive-noise variance such that $x:=\xi/(N+1)\le1$. Split the line into $N+1$ additive-noise links, each with variance $x$. For a link of variance $y\in(0,1]$, use the constructed Gaussian resource and comparison states of (8)–(11) and (28) with $\eta=1$ and $r=-\tfrac12\ln y$, and write $\Psi(\mathcal E_y)=S(\sigma_y\Vert\widetilde\sigma_{y,\rm sep})$ in bits. Define the chain comparison value as in (39), namely the minimum of these link divergences. Then
--   $$
--   \Psi(\{\mathcal E_i\}_{i=0}^{N})
--   =\min_{0\le i\le N}\Psi(\mathcal E_{\xi/(N+1)})
--   =\Psi(\mathcal E_{\xi/(N+1)}).
--   $$
--   This is the displayed algebraic specialization for any number of repeaters. It includes $N=0$, with one link, and makes no claim that the placement optimizes an operational capacity or that a rate is achievable.
-- source:
--   Finite-resource teleportation stretching for continuous-variable systems, arXiv:1706.06065v3, PDF p. 6, V, specialization after Eq. (39)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P69

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P69

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance covarianceCharacteristicValue
   multimodeWeylTrace standardFormCovariance vacuumKernel)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01 (generalizedRelativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.06065v3, PDF p.6, after (39): equal-noise chain specialization.
All N+1 links have noise xi/(N+1); the local resources are exactly those in
(8)--(11), (28)--(29). No optimal-placement or achievability claim is made. -/
theorem equalNoiseChainComparison
    (N : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (hlink : xi / ((N : ℝ) + 1) ≤ 1) :
    additiveChainComparisonBound N (fun _ => xi / ((N : ℝ) + 1)) =
      additiveComparisonBound (xi / ((N : ℝ) + 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P69

end
