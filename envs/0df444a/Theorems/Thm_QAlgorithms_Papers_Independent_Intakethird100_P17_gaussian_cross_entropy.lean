-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P17_gaussian_cross_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P17.gaussian_cross_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:25:24.939136+00:00
-- url     : https://prove2.me/theorems/132c336a-7f1a-4aab-903d-b3f39b57ba9e
-- title:
--   Gaussian cross entropy in general quadrature conventions
-- statement:
--   Let $n\ge0$, $\kappa>0$, and let $\rho_j=\rho(\sigma_j,u_j)$, $j=1,2$, be normalized finite-energy Gaussian densities on the full $n$-mode oscillator space, with arbitrary finite means $u_j\in\mathbb R^{2n}$ and centered half-anticommutator covariances $\sigma_j$. The quadratures satisfy $[q,q^T]=i\Omega/\kappa$, where $\Omega$ is the direct sum of the canonical two-dimensional antisymmetric form. Assume each symplectic eigenvalue of each covariance is strictly greater than $1/(2\kappa)$. Put $\delta=u_2-u_1$ and $G_2=2i\Omega\operatorname{arcoth}(2\kappa\sigma_2 i\Omega)$. Then the cross entropy is finite and
--
--   $$
--   -\operatorname{Tr}(\rho_1\log_2\rho_2)
--   =\Sigma_\kappa(\sigma_1,\sigma_2,\delta)
--   :=\frac{\ln\det(\kappa\sigma_2+i\Omega/2)+\kappa\operatorname{tr}(\sigma_1G_2)+\kappa\delta^TG_2\delta}{2\ln2}.
--   $$
--
--   A simultaneous displacement of both states gives the centered calculation in (A18). The identity does not require commuting covariance matrices or commuting density operators.
--
--   **Formalization Note** Cross entropy is independently computed from bounded support-log cutoffs of the actual density operator. The theorem asserts convergence to the displayed expression; the matrix inverse-coth series also has an explicit convergence conclusion.
-- source:
--   Tight bounds for private communication over bosonic Gaussian channels based on teleportation simulation with optimal finite resources, arXiv:1808.00608v4, PDF p. 7, Appendix A Eqs. (A18)–(A19): Gaussian cross entropy in κ conventions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P17

noncomputable section

open Filter

open scoped BigOperators ENNReal ComplexOrder Topology Matrix

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P17

open QAlgorithms.Papers.Independent.Claimed50.P30
  (ModeOperator Quadrature PhaseVector numberKet trace TraceSummable
   FockWeylSystem GaussianMoments canonicalOmega)

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass relativeEntropy)

open QAlgorithms.Papers.Independent.Next46.P17 (raisingCoefficient)

/-- arXiv:1808.00608v4, Appendix A, PDF p.7, (A18)--(A19).
Arbitrary finite means; strict Gibbs domain for both covariances. The common
displacement leaves delta=u2-u1; no commuting-covariance premise is imposed. -/
theorem gaussian_cross_entropy {n : ℕ}
    (W : FockWeylSystem n) (kappa : ℝ) (hkappa : 0 < kappa)
    (rho1 rho2 : ModeOperator n) (u1 u2 : PhaseVector n)
    (sigma1 sigma2 : Matrix (Quadrature n) (Quadrature n) ℝ)
    (h1 : GaussianInConvention W kappa rho1 u1 sigma1)
    (h2 : GaussianInConvention W kappa rho2 u2 sigma2)
    (hs1 : StrictGibbsCovariance kappa sigma1)
    (hs2 : StrictGibbsCovariance kappa sigma2) :
    Summable (gibbsSeriesTerm kappa sigma1) ∧
    Summable (gibbsSeriesTerm kappa sigma2) ∧
    (∀ k, TraceSummable (rho1.comp (oscillatorLogCutoff rho2 k))) ∧
    Tendsto (crossEntropyCutoff rho1 rho2) atTop
      (nhds (gaussianSigma kappa sigma1 sigma2 (u2 - u1))) ∧
    oscillatorCrossEntropy rho1 rho2 = gaussianSigma kappa sigma1 sigma2 (u2 - u1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P17

end
