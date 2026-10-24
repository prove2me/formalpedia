-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_conformal_multimode_multiplicative
-- name    : QAlgorithms.Papers.Independent.Support50.P28.conformal_multimode_multiplicative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:19:32.248185+00:00
-- url     : https://prove2.me/theorems/c12a61ea-6f66-4abf-87a0-e1c385cfa5b8
-- title:
--   Section V final unnumbered result: conformally symplectic multimode factors
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   Let $r\ge1$ and let $\Phi_i=\Phi_{X_i,Y_i}$ act on $m_i\ge1$ modes. Suppose $X_i=x_i S_i$, where $x_i>0$ and $S_i^T\sigma_i S_i=\sigma_i$, with $\sigma_i$ the canonical form on those modes. Then for every real $p>1$,
--
--   $$\xi_p\!\left(\bigotimes_{i=1}^r\Phi_i\right)=\prod_{i=1}^r\xi_p(\Phi_i).$$
--
--   This is the explicit last-paragraph scope in Section V. The scalars need not agree, and the noise matrices need not be positive definite. The paper's explanation through Proposition 2 does not establish the unequal-scalar case as written; that proof issue is recorded without adding an absent hypothesis.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 7, Section V final unnumbered result: conformally symplectic multimode factors

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P28

noncomputable section

open scoped BigOperators ENNReal ComplexOrder Matrix

namespace QAlgorithms.Papers.Independent.Support50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation gaussianStateCharacteristic singleCharacteristic weylKernel)

open QAlgorithms.Papers.Independent.Claimed50.P30 (phiMinus)

/-- PDF p.7, last paragraph: the written conformally symplectic multimode
scope, without equality of the positive scalar factors and without Y>0.
The source's claimed implication from Proposition 2 is an incomplete proof route;
the explicit statement is retained unchanged, with this issue recorded. -/
theorem conformal_multimode_multiplicative {r : ℕ} (hr : 0 < r)
    (m : Fin r → ℕ) (hm : ∀ i, 0 < m i)
    (E : (i : Fin r) → CenteredOscillatorChannel (Fin (m i)))
    (x : Fin r → ℝ) (hx : ∀ i, 0 < x i)
    (S : (i : Fin r) → OscillatorCovariance (Fin (m i)))
    (hS : ∀ i, PreservesInterleavedSigma (S i)) (hX : ∀ i, (E i).X = x i • S i)
    (p : ℝ) (hp : 1 < p) : GaussianPurityMultiplicative p E := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
