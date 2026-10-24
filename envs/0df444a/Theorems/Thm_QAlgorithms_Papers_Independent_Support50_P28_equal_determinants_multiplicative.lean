-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_equal_determinants_multiplicative
-- name    : QAlgorithms.Papers.Independent.Support50.P28.equal_determinants_multiplicative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:17:42.3124+00:00
-- url     : https://prove2.me/theorems/fcb7dbbd-0b8a-4e87-a909-f8e79edd42ae
-- title:
--   Proposition 2: equal determinant, positive-noise one-mode factors
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   Let $r\ge1$ and let $\Phi_i=\Phi_{X_i,Y_i}$ be single-mode Gaussian channels. Assume that every $Y_i$ is positive definite in the Loewner sense and that $\det X_i=\det X_j$ for all $i,j$. Then for every real $p>1$,
--
--   $$\xi_p\!\left(\bigotimes_{i=1}^r\Phi_i\right)=\prod_{i=1}^r\xi_p(\Phi_i).$$
--
--   The common determinant may be positive, negative, or zero. This extends multiplicativity from identical channels to different one-mode factors with equal determinants; no invertibility assumption is added.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 6, Proposition 2: equal determinant, positive-noise one-mode factors

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

/-- PDF pp.6--7, Proposition 2: strict Loewner positivity of every noise matrix
and equality of the REAL determinants; the common determinant may be zero or negative. -/
theorem equal_determinants_multiplicative {r : ℕ} (hr : 0 < r)
    (E : Fin r → CenteredOscillatorChannel (Fin 1))
    (hY : ∀ i, (E i).Y.PosDef) (hX : ∀ i j, (E i).X.det = (E j).X.det)
    (p : ℝ) (hp : 1 < p) : GaussianPurityMultiplicative p E := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
