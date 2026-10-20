-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P25_identical_state_testing
-- name    : QAlgorithms.Papers.Independent.Frontier30.P25.identical_state_testing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:41:03.022075+00:00
-- url     : https://prove2.me/theorems/6084e370-9609-48b0-8883-1311f5af8557
-- title:
--   Hypothesis testing against the same state
-- statement:
--   Let $\rho$ be a density operator on a nonzero finite-dimensional Hilbert space, and let $0\le\varepsilon<1$. Define the hypothesis-testing divergence in bits by $D_H^\varepsilon(\rho\Vert\sigma)=-\log_2\inf\{\operatorname{Tr}(M\sigma):0\le M\le I,\ \operatorname{Tr}(M\rho)\ge1-\varepsilon\}$, allowing infinite divergence when the infimum is zero. Then
--
--   $$D_H^\varepsilon(\rho\Vert\rho)=-\log_2(1-\varepsilon).$$
--
--   Normalization and the strict upper bound on $\varepsilon$ ensure the real logarithm has a positive argument. This identity supplies the testing value for the entanglement-breaking converse.
-- source:
--   Converse bounds for private communication over quantum channels, arXiv:1602.08898v3, PDF p. 15, (4.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P25

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Pinned accepted definitions; assessments record the domains of equivalence.

open QAlgorithms.Papers.Independent.Dependency50.P09 (OneDesign relativeD sandwichedD)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits idealCCQ)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity privateState privacyTest)

/-- PDF p.15, (4.2): identical normalized states; epsilon<1 guards log(1-epsilon). -/
theorem identical_state_testing
    {I : Type*} [Fintype I] [Nonempty I]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps < 1) :
    testingD eps rho rho = (-logBits (1 - eps) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P25

end
