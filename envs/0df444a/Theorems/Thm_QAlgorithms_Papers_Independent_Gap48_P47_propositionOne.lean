-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P47_propositionOne
-- name    : QAlgorithms.Papers.Independent.Gap48.P47.propositionOne
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:08:08.737478+00:00
-- url     : https://prove2.me/theorems/c7aeb4b6-bb20-4c36-aff7-59cfaa5f0934
-- title:
--   Proposition 1: one noisy local operation with reversible local changes
-- statement:
--   Let $\rho,\rho''$ be normalized two-mode Gaussian oscillator states with finite second moments, arbitrary first moments, and associated vectors $\xi=(\xi_1,\xi_2,\xi_3,\xi_4)$ and $\xi''=(\xi''_1,\xi_2,\xi''_3,\xi''_4)$. Assume $\xi_4,\xi''_4>0$. Covariances use $\hbar=1$ and vacuum covariance $I$.
--
--   A LOG channel acts on Alice, and Bob is allowed a reversible local Gaussian unitary and translation, as in the source's proof. Each channel is defined on all trace-class inputs. With
--   $$
--   g(a,b,c,d)=(a^2-1)+(b^2-1)c^2d^2+2cd-ab(c^2+d^2),\qquad
--   f_1(x,y)=g(\xi''_1,\xi_1,x/\xi_3,y/\xi_4),
--   $$
--   the conversion is possible precisely when
--   $$
--   \frac{|\xi''_3\xi''_4|}{\xi''_1}\le
--   \frac{|\xi_3\xi_4|}{\xi_1},\qquad
--   f_1(\xi''_3,\xi''_4)\ge0.
--   $$
--   This criterion characterizes one noisy local step while retaining the independent reversible changes used to pass to and from normal form.
-- source:
--   Conditions for the local manipulation of Gaussian states, arXiv:quant-ph/0109126v2, PDF p. 2, Proposition 1

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

/-- Proposition 1, PDF p.2, interpreted by its proof on pp.2--3: one noisy
local operation and free reversible local symplectic changes. -/
theorem propositionOne (rho target : TwoModeGaussianDensity)
    (hsource : 0 < (associatedVector rho.covariance).four)
    (htarget : 0 < (associatedVector target.covariance).four)
    (hsecond : (associatedVector target.covariance).two =
      (associatedVector rho.covariance).two) :
    LOGInSystemOne rho target ↔
      |(associatedVector target.covariance).three *
        (associatedVector target.covariance).four| /
        (associatedVector target.covariance).one ≤
      |(associatedVector rho.covariance).three *
        (associatedVector rho.covariance).four| /
        (associatedVector rho.covariance).one ∧
      0 ≤ f1 rho.covariance target.covariance
        (associatedVector target.covariance).three
        (associatedVector target.covariance).four := by sorry

end QAlgorithms.Papers.Independent.Gap48.P47

end
