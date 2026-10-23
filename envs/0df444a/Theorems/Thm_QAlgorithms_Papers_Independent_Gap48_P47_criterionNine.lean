-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P47_criterionNine
-- name    : QAlgorithms.Papers.Independent.Gap48.P47.criterionNine
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:08:38.679736+00:00
-- url     : https://prove2.me/theorems/19610171-3389-4912-9f54-c016b382cebb
-- title:
--   Equation (9): two-dimensional LOG feasibility criterion
-- statement:
--   Let $\rho,\rho'$ be normalized two-mode Gaussian oscillator states with finite second moments and arbitrary means. Use $\hbar=1$, vacuum covariance $I$, and associated normal vectors $\xi,\xi'$ with $\xi_4,\xi'_4>0$. Define
--   $$
--   g(a,b,c,d)=(a^2-1)+(b^2-1)c^2d^2+2cd-ab(c^2+d^2),
--   $$
--   $$
--   f_1(x,y)=g(\xi'_1,\xi_1,x/\xi_3,y/\xi_4),\quad
--   f_2(x,y)=g(\xi'_2,\xi_2,\xi'_3/x,\xi'_4/y),
--   $$
--   and $w_1=|\xi_3\xi_4|\xi'_1/\xi_1$, $w_2=|\xi'_3\xi'_4|\xi_2/\xi'_2$. Then
--   $$
--   \rho\longrightarrow\rho'\text{ under LOG}
--   \quad\Longleftrightarrow\quad
--   \exists x>0,\ y\in\mathbb R:\quad
--   w_2\le|xy|\le w_1,\quad f_1(x,y)\ge0,\quad f_2(x,y)\ge0.
--   $$
--   LOG consists of independent finite-ancilla local Gaussian dilations and partial traces on the actual density operators. No restriction $x\ge|y|$ is imposed. The positive lower product bound excludes zero divisors.
--
--   This is the alternative feasibility criterion before reducing the search to simultaneous zero sets.
-- source:
--   Conditions for the local manipulation of Gaussian states, arXiv:quant-ph/0109126v2, PDF p. 3, Eq. (9)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Gap48.P47

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel GaussianWithCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue modeCovarianceBlock
   standardFormCovariance)

open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P14 (boundedUnitaryConjugation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, (9): the alternative two-dimensional inequality criterion.
No ordering constraint x>=|y| is inserted. -/
theorem criterionNine (rho target : TwoModeGaussianDensity)
    (hsource : 0 < (associatedVector rho.covariance).four)
    (htarget : 0 < (associatedVector target.covariance).four) :
    LOGReachable rho target ↔
      ∃ x y : ℝ, 0 < x ∧
        w2 rho.covariance target.covariance ≤ |x * y| ∧
        |x * y| ≤ w1 rho.covariance target.covariance ∧
        0 ≤ f1 rho.covariance target.covariance x y ∧
        0 ≤ f2 rho.covariance target.covariance x y := by sorry

end QAlgorithms.Papers.Independent.Gap48.P47

end
