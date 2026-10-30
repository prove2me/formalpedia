-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P18_gaussian_logLikelihoodMoments_finite
-- name    : QAlgorithms.Papers.Independent.Bridge50.P18.gaussian_logLikelihoodMoments_finite
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:52:45.265408+00:00
-- url     : https://prove2.me/theorems/a2ae0ff3-5d56-451b-9024-01b364ddac6f
-- title:
--   Finite spectral log-likelihood moments of centered Gaussian states
-- statement:
--   Let $m\ge1$ be a finite number of oscillator modes, and let $\rho$ and $\sigma$ be faithful, centered Gaussian states with finite actual mean total photon number on the full completed $m$-mode Fock space. The covariance convention uses the full anticommutator, so vacuum covariance is $I$ and $[q_j,p_k]=i\delta_{jk}$. For complete spectral decompositions, let $L=\log_2(\lambda_x/\mu_y)$ have probability $\lambda_x|\langle\psi_y|\phi_x\rangle|^2$, and let $D=\mathbb E L$.
--
--   Then the first moment exists absolutely and
--
--   $$
--   D(\rho\|\sigma)<\infty,\qquad V(\rho\|\sigma)=\mathbb E|L-D|^2<\infty,\qquad T(\rho\|\sigma)=\mathbb E|L-D|^3<\infty.
--   $$
--
--   These finiteness statements supply the moment hypotheses for the second-order hypothesis-testing converse when the additional positive-variance condition holds. Equal states are allowed here; no fourth-moment assumption is imposed.
--
--   **Formalization Note** Gaussianity is enforced through the actual convergent oscillator Weyl characteristic with a symmetric physical covariance. The spectral third absolute moment is not replaced by a noncommutative operator cube.
-- source:
--   Upper bounds on secret key agreement over lossy thermal bosonic channels, arXiv:1706.04590v2, PDF p. 13, Appendix D, final conclusion; (33)–(36),(39)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P18

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P18

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (operatorTrace)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo tensorPower)

open QAlgorithms.Papers.Independent.Support50.P20 (hilbertTestingDivergence)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov GaussianWithCovariance multimodeWeylTrace covarianceCharacteristicValue)

-- The accepted complete coordinate basis has the identical body and type.

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

/-- PDF pp.5--6 and Appendix D, pp.12--13: finite D,V,T for every positive
finite number of modes and distinct or equal faithful centered Gaussian states.
In particular rho=sigma is permitted and no positive-variance or fourth-moment
premise is supplied. -/
theorem gaussian_logLikelihoodMoments_finite {m : ℕ} (hm : 0 < m)
    {K J : Type} [Countable K] [Countable J]
    (rho sigma : State (Fin m → ℕ))
    (r : StateSpectrum K rho.coefficients) (s : StateSpectrum J sigma.coefficients)
    (hr : ∀ k, 0 < r.value k) (hs : ∀ j, 0 < s.value j)
    (hrho : CenteredFiniteEnergyGaussian rho)
    (hsigma : CenteredFiniteEnergyGaussian sigma) :
    Summable (meanSummand r s) ∧ centralMomentBits r s 2 < ⊤ ∧
      centralMomentBits r s 3 < ⊤ := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P18

end
