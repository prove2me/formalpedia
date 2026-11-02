-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P17_gaussian_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P17.gaussian_relative_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:26:05.315732+00:00
-- url     : https://prove2.me/theorems/ce5b93e9-99e6-4132-8a78-21966833e55e
-- title:
--   Gaussian Umegaki relative entropy with arbitrary means
-- statement:
--   Let $n\ge0$, $\kappa>0$, and let $\rho_j=\rho(\sigma_j,u_j)$, $j=1,2$, be normalized finite-energy Gaussian densities on the full $n$-mode oscillator space. Covariances are centered half-anticommutator covariances, means $u_j\in\mathbb R^{2n}$ are arbitrary, and $[q,q^T]=i\Omega/\kappa$ for the canonical interleaved symplectic form $\Omega$. Assume all symplectic eigenvalues of both covariances exceed $1/(2\kappa)$. For $G_j=2i\Omega\operatorname{arcoth}(2\kappa\sigma_j i\Omega)$, define
--
--   $$
--   \Sigma_\kappa(S,T,d)=\frac{\ln\det(\kappa T+i\Omega/2)+\kappa\operatorname{tr}(S G_T)+\kappa d^T G_Td}{2\ln2},\qquad G_T=2i\Omega\operatorname{arcoth}(2\kappa T i\Omega).
--   $$
--
--   The independently defined Umegaki relative entropy in bits is finite and satisfies
--
--   $$
--   S(\rho_1\Vert\rho_2)=-\Sigma_\kappa(\sigma_1,\sigma_1,0)+\Sigma_\kappa(\sigma_1,\sigma_2,u_2-u_1).
--   $$
--
--   This general-mean identity specializes to the main-text zero-mean formula when $\kappa=1/2$.
--
--   **Formalization Note** The left side uses the accepted extended operator relative entropy, converted from nats to bits. Finiteness and nonnegativity are conclusions, so conversion to a real value cannot erase a support failure.
-- source:
--   Tight bounds for private communication over bosonic Gaussian channels based on teleportation simulation with optimal finite resources, arXiv:1808.00608v4, PDF p. 7, Appendix A Eq. (A20): general-mean Gaussian relative entropy on its finite Gibbs domain

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

/-- arXiv:1808.00608v4, Appendix A, PDF p.7, (A20).
Equality to independently defined extended Umegaki relative entropy in bits;
its finiteness is concluded. Singular/pure Gibbs boundary is separately deferred. -/
theorem gaussian_relative_entropy {n : ℕ}
    (W : FockWeylSystem n) (kappa : ℝ) (hkappa : 0 < kappa)
    (rho1 rho2 : ModeOperator n) (u1 u2 : PhaseVector n)
    (sigma1 sigma2 : Matrix (Quadrature n) (Quadrature n) ℝ)
    (h1 : GaussianInConvention W kappa rho1 u1 sigma1)
    (h2 : GaussianInConvention W kappa rho2 u2 sigma2)
    (hs1 : StrictGibbsCovariance kappa sigma1)
    (hs2 : StrictGibbsCovariance kappa sigma2) :
    let D := oscillatorRelativeEntropy rho1 rho2 h1.1.1.1 h2.1.1.1
    let expression := -gaussianSigma kappa sigma1 sigma1 0 +
      gaussianSigma kappa sigma1 sigma2 (u2 - u1)
    Summable (gibbsSeriesTerm kappa sigma1) ∧
    Summable (gibbsSeriesTerm kappa sigma2) ∧
    D < ⊤ ∧ 0 ≤ expression ∧ D.toReal = expression := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P17

end
