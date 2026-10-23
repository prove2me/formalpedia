-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P47_propositionTwo
-- name    : QAlgorithms.Papers.Independent.Gap48.P47.propositionTwo
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:07:33.286655+00:00
-- url     : https://prove2.me/theorems/90484063-131a-416b-a3b9-c4ed69c63b42
-- title:
--   Proposition 2: exact LOG conversion criterion
-- statement:
--   Let $\rho$ and $\rho'$ be normalized Gaussian density operators on the completed two-mode oscillator Hilbert space, with finite second moments and covariances $\Gamma,\Gamma'$ in the convention $[X_j,P_k]=i\delta_{jk}$ and vacuum covariance $I$. Let $\xi=(\xi_1,\xi_2,\xi_3,\xi_4)$ and $\xi'$ be their associated local symplectic normal-form vectors, with $\xi_4,\xi'_4>0$. First moments are arbitrary.
--
--   Write
--   $$
--   g(a,b,c,d)=(a^2-1)+(b^2-1)c^2d^2+2cd-ab(c^2+d^2),
--   $$
--   $$
--   f_1(x,y)=g(\xi'_1,\xi_1,x/\xi_3,y/\xi_4),\qquad
--   f_2(x,y)=g(\xi'_2,\xi_2,\xi'_3/x,\xi'_4/y).
--   $$
--   Define $w_1=|\xi_3\xi_4|\xi'_1/\xi_1$ and $w_2=|\xi'_3\xi'_4|\xi_2/\xi'_2$. Then
--   $$
--   \rho\longrightarrow\rho'\text{ under LOG}
--   \quad\Longleftrightarrow\quad
--   \exists x>0,\ y\in\mathbb R:\quad
--   f_1(x,y)=f_2(x,y)=0,\qquad w_2\le |xy|\le w_1.
--   $$
--   Here LOG means a product of two independent local channels, each implemented by a finite Gaussian ancilla, a local Gaussian unitary and a partial trace. The selected channels act on every trace-class input; their output on the specified input equals the target density operator. Because $w_2>0$, the feasible points have $x,y\ne0$.
--
--   The criterion reduces actual Gaussian state conversion to intersection of two explicitly defined zero loci.
-- source:
--   Conditions for the local manipulation of Gaussian states, arXiv:quant-ph/0109126v2, PDF p. 2, Proposition 2

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

/-- Proposition 2, PDF p.2, proof p.3: the full LOG criterion, retaining the
printed strict positivity of both fourth normal coordinates. -/
theorem propositionTwo (rho target : TwoModeGaussianDensity)
    (hsource : 0 < (associatedVector rho.covariance).four)
    (htarget : 0 < (associatedVector target.covariance).four) :
    LOGReachable rho target ↔
      ∃ x y : ℝ, 0 < x ∧
        f1 rho.covariance target.covariance x y = 0 ∧
        f2 rho.covariance target.covariance x y = 0 ∧
        w2 rho.covariance target.covariance ≤ |x * y| ∧
        |x * y| ≤ w1 rho.covariance target.covariance := by sorry

end QAlgorithms.Papers.Independent.Gap48.P47

end
