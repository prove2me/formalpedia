-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P22_squashed_improvedContinuity
-- name    : QAlgorithms.Papers.Independent.Gap48.P22.squashed_improvedContinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:16:31.115553+00:00
-- url     : https://prove2.me/theorems/c8d2401a-17d8-4f55-bb89-68286f271dfd
-- title:
--   Improved continuity bound for squashed entanglement
-- statement:
--   Let $\rho^{AB},\sigma^{AB}$ be density operators on the same finite positive-dimensional systems. Suppose $0\le\varepsilon\le1$ and $\tfrac12\|\rho-\sigma\|_1\le\varepsilon$. With bit-valued squashed entanglement, taking every positive finite extension dimension, and binary entropy $h_2$ in bits,
--
--   $$|E_{\rm sq}(\rho)-E_{\rm sq}(\sigma)|\le4\varepsilon\log_2\dim A+2(1+\varepsilon)h_2\!\left(\frac{\varepsilon}{1+\varepsilon}\right).$$
--
--   This is the paper's improved uniform continuity estimate. It includes identical states at $\varepsilon=0$ and uses the half trace-distance hypothesis.
-- source:
--   Squashed entanglement, k-extendibility, quantum Markov chains, and recovery maps, arXiv:1410.4184v4, PDF p. 5, Unnumbered improved continuity bound

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Gap48.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement KExtendible)

open QAlgorithms.Papers.Independent.Claimed50.P33
  (RegisterBasis registerMarginal entropyAt conditionalMultipartiteInformation singleParties
   forgetEnvironment)

open QAlgorithms.Papers.Independent.Renew46.P35 (classicalCMI)

open QAlgorithms.Entanglement (IsSeparableDensity)

/-- Improved unnumbered continuity bound, PDF p.5. The PDF prints absolute
value bars, which are missing in the extracted text; no square root of epsilon occurs. -/
theorem squashed_improvedContinuity {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (hdistance : traceDistance rho sigma ≤ epsilon) :
    |squashedEntanglement rho - squashedEntanglement sigma| ≤
      4 * epsilon * Real.logb 2 (Fintype.card A) +
        2 * (1+epsilon) * binEntropy2 (epsilon/(1+epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P22

end
