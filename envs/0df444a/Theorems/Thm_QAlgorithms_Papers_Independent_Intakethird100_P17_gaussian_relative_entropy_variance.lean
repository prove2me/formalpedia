-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P17_gaussian_relative_entropy_variance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P17.gaussian_relative_entropy_variance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:27:03.604483+00:00
-- url     : https://prove2.me/theorems/ac370b3a-e5be-4cde-917c-aaffcfbc9bfe
-- title:
--   Gaussian relative entropy variance
-- statement:
--   Let $n\ge0$, $\kappa>0$, and let $\rho_j=\rho(\sigma_j,u_j)$, $j=1,2$, be normalized finite-energy Gaussian densities on the full $n$-mode oscillator space. The centered half-anticommutator covariance convention is $[q,q^T]=i\Omega/\kappa$, with canonical interleaved $\Omega$. Assume every symplectic eigenvalue of each covariance exceeds $1/(2\kappa)$; both finite mean vectors are arbitrary. Write $G_j=2i\Omega\operatorname{arcoth}(2\kappa\sigma_j i\Omega)$, $\widetilde G=G_1-G_2$, $\delta=u_1-u_2$, $B=8\kappa^2G_2\sigma_1G_2$, and $S=S(\rho_1\Vert\rho_2)$ in bits. Then $S$ and the centered operator log-likelihood variance are finite, and
--
--   $$
--   \begin{aligned}
--   V(\rho_1\Vert\rho_2)
--   &:=\operatorname{Tr}\!\left[\rho_1(\log_2\rho_1-\log_2\rho_2-S)^2\right]\\
--   &=\frac{4\kappa^2\operatorname{tr}(\sigma_1\widetilde G\sigma_1\widetilde G)+\operatorname{tr}(\widetilde G\Omega\widetilde G\Omega)+\delta^TB\delta}{2(2\ln2)^2}.
--   \end{aligned}
--   $$
--
--   The positive sign before the term containing two copies of $\Omega$ is part of the formula. The variance vanishes for identical states.
--
--   **Formalization Note** The left side is the convergent density-weighted limit of the square of the actual centered operator log difference. The order of multiplication is retained; this is not a classical variance that assumes the operators commute.
-- source:
--   Tight bounds for private communication over bosonic Gaussian channels based on teleportation simulation with optimal finite resources, arXiv:1808.00608v4, PDF p. 8, Appendix A final unnumbered formula: relative entropy variance

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

/-- arXiv:1808.00608v4, Appendix A, PDF p.8, final unnumbered formula.
Variance of the actual centered NONCOMMUTATIVE operator log difference.
Both covariances have finite Gibbs matrices; all means are allowed. -/
theorem gaussian_relative_entropy_variance {n : ℕ}
    (W : FockWeylSystem n) (kappa : ℝ) (hkappa : 0 < kappa)
    (rho1 rho2 : ModeOperator n) (u1 u2 : PhaseVector n)
    (sigma1 sigma2 : Matrix (Quadrature n) (Quadrature n) ℝ)
    (h1 : GaussianInConvention W kappa rho1 u1 sigma1)
    (h2 : GaussianInConvention W kappa rho2 u2 sigma2)
    (hs1 : StrictGibbsCovariance kappa sigma1)
    (hs2 : StrictGibbsCovariance kappa sigma2) :
    let D := oscillatorRelativeEntropy rho1 rho2 h1.1.1.1 h2.1.1.1
    let expression := gaussianVarianceExpression kappa sigma1 sigma2 (u1 - u2)
    Summable (gibbsSeriesTerm kappa sigma1) ∧
    Summable (gibbsSeriesTerm kappa sigma2) ∧ D < ⊤ ∧
    (∀ k, let L := oscillatorLogCutoff rho1 k - oscillatorLogCutoff rho2 k -
        (D.toReal : ℂ) • (1 : ModeOperator n)
      TraceSummable (rho1.comp (L.comp L))) ∧
    Tendsto (relativeVarianceCutoff rho1 rho2 D.toReal) atTop (nhds expression) ∧
    oscillatorRelativeVariance rho1 rho2 D.toReal = expression := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P17

end
