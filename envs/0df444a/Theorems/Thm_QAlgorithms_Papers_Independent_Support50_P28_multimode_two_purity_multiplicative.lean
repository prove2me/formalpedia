-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_multimode_two_purity_multiplicative
-- name    : QAlgorithms.Papers.Independent.Support50.P28.multimode_two_purity_multiplicative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:18:18.205463+00:00
-- url     : https://prove2.me/theorems/ebd14ae1-0cc4-471f-835d-e1d846cc6cf8
-- title:
--   Proposition 3: arbitrary invertible multimode factors at p=2
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   Let $r\ge1$ and let $\Phi_i=\Phi_{X_i,Y_i}$ be Gaussian channels, where factor $i$ acts on $m_i\ge1$ complete modes. Assume $\det X_i\ne0$ for every $i$. Then
--
--   $$\xi_2\!\left(\bigotimes_{i=1}^r\Phi_i\right)=\prod_{i=1}^r\xi_2(\Phi_i).$$
--
--   The partition is by channels, each of which may have several modes. No equal-sign, equal-determinant, or positive-definite-noise hypothesis is imposed. The norm here is the Schatten $2$-norm, whose square is ordinary purity.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 7, Proposition 3: arbitrary invertible multimode factors at p=2

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

/-- PDF p.7, Proposition 3: arbitrary invertible multimode channel factors at
p=2. No equal-sign, equal-determinant or strictly positive noise restriction. -/
theorem multimode_two_purity_multiplicative {r : ℕ} (hr : 0 < r)
    (m : Fin r → ℕ) (hm : ∀ i, 0 < m i)
    (E : (i : Fin r) → CenteredOscillatorChannel (Fin (m i)))
    (hX : ∀ i, (E i).X.det ≠ 0) : GaussianPurityMultiplicative 2 E := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
