-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_singular_factors
-- name    : QAlgorithms.Papers.Independent.Support50.P28.singular_factors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:15:18.410367+00:00
-- url     : https://prove2.me/theorems/43940201-f457-4e6b-af72-a8874a9d8de4
-- title:
--   Section V remark after Lemma 2: zero-determinant factors
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   Let $r\ge1$ and let $\Phi_i=\Phi_{X_i,Y_i}$ be single-mode Gaussian channels with $\det X_i=0$ for every $i$. For every real $p>1$, their tensor product is multiplicative. Moreover, if another physical single-mode family $\Psi_i=\Phi_{X_i',Y_i}$ has the same noise matrices and $\det X_i'=0$ for every $i$, then
--
--   $$\xi_p\!\left(\bigotimes_i\Phi_i\right)=\prod_i\xi_p(\Phi_i),\qquad
--   \xi_p\!\left(\bigotimes_i\Phi_i\right)=\xi_p\!\left(\bigotimes_i\Psi_i\right).$$
--
--   Thus the supremum in this regime depends only on the noise, not on the zero-determinant matrices $X_i$. Infinite squeezing may approximate the supremum without attaining it.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 5, Section V remark after Lemma 2: zero-determinant factors

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

/-- PDF p.5, remark after Lemma 2: all-zero determinant factors are multiplicative
and the supremum does not depend on X. Comparison to every physical family with
the same Y expresses independence without assuming attainment. -/
theorem singular_factors {r : ℕ} (hr : 0 < r)
    (E : Fin r → CenteredOscillatorChannel (Fin 1)) (hzero : ∀ i, (E i).X.det = 0)
    (p : ℝ) (hp : 1 < p) :
    GaussianPurityMultiplicative p E ∧
    ∀ F : Fin r → CenteredOscillatorChannel (Fin 1),
      (∀ i, (F i).X.det = 0 ∧ (F i).Y = (E i).Y) →
      maximalOutputPurity p (tensorOscillatorChannel E) = maximalOutputPurity p (tensorOscillatorChannel F) := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
