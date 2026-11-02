-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P17_gaussian_quadratic_moments
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P17.gaussian_quadratic_moments
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:24:35.930205+00:00
-- url     : https://prove2.me/theorems/60bd199b-567a-40b0-9a00-9bffd00fe55a
-- title:
--   Gaussian quadratic mean, second moment, and variance
-- statement:
--   Let $n\ge0$ and $\kappa>0$. On the full $n$-mode oscillator space, let $\rho$ be a normalized, centered, finite-energy Gaussian density with centered half-anticommutator covariance $\sigma$. Write $q=(x_1,p_1,\ldots,x_n,p_n)^T$, with $[q,q^T]=i\Omega/\kappa$ and $\Omega=\bigoplus_{j=1}^n\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$. For every real symmetric $2n\times2n$ matrix $A$, set $Q=q^TAq$. The polynomial products and density-weighted traces converge, and
--
--   $$
--   \begin{aligned}
--   \mathbb E_\rho Q&=\operatorname{tr}(\sigma A),\\
--   \mathbb E_\rho Q^2&=\operatorname{tr}(\sigma A)^2+2\operatorname{tr}(A\sigma A\sigma)-\frac{\operatorname{tr}(A\Omega A\Omega^T)}{2\kappa^2},\\
--   \operatorname{Var}_\rho Q&=2\operatorname{tr}(A\sigma A\sigma)+\frac{\operatorname{tr}(A\Omega A\Omega)}{2\kappa^2}.
--   \end{aligned}
--   $$
--
--   These identities include pure Gaussian states and provide the quadratic moments needed for the entropy-variance calculation.
--
--   **Formalization Note** The observables use their actual creation/annihilation coefficients on the full finite-particle core. Absolute convergence of the infinite pairings is a conclusion, rather than an assumed moment identity.
-- source:
--   Tight bounds for private communication over bosonic Gaussian channels based on teleportation simulation with optimal finite resources, arXiv:1808.00608v4, PDF p. 7, Appendix A Eqs. (A8),(A11),(A12): Gaussian quadratic moments

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

/-- arXiv:1808.00608v4, Appendix A, PDF p.7, (A8),(A11),(A12).
Real symmetric A and actual centered normalized Gaussian densities, including
pure states. All polynomial traces and core products converge. -/
theorem gaussian_quadratic_moments {n : ℕ}
    (W : FockWeylSystem n) (kappa : ℝ) (hkappa : 0 < kappa)
    (rho : ModeOperator n) (sigma A : Matrix (Quadrature n) (Quadrature n) ℝ)
    (hrho : GaussianInConvention W kappa rho 0 sigma) (hA : A.transpose = A) :
    let Q := quadraticKernel kappa A
    let Omega := canonicalOmega n
    (∀ a b : Quadrature n, PolynomialProductSummable (quadratureKernel kappa a) (quadratureKernel kappa b)) ∧
    PolynomialProductSummable Q Q ∧
    PolynomialPairingSummable rho Q ∧
    PolynomialPairingSummable rho (polynomialKernelProduct Q Q) ∧
    polynomialExpectation rho Q = (sigma * A).trace ∧
    polynomialExpectation rho (polynomialKernelProduct Q Q) =
      (sigma * A).trace ^ 2 + 2 * (A * sigma * A * sigma).trace -
        (A * Omega * A * Omega.transpose).trace / (2 * kappa ^ 2) ∧
    quadraticVariance rho kappa A = 2 * (A * sigma * A * sigma).trace +
      (A * Omega * A * Omega).trace / (2 * kappa ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P17

end
