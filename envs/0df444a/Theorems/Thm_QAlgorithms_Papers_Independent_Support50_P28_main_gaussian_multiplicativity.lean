-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_main_gaussian_multiplicativity
-- name    : QAlgorithms.Papers.Independent.Support50.P28.main_gaussian_multiplicativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:12:10.8837+00:00
-- url     : https://prove2.me/theorems/885aa074-4556-48d3-9354-af9a69d26211
-- title:
--   Abstract/main result: Gaussian maximal-output-purity multiplicativity
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   The abstract's multiplicativity assertion has the following three precise scopes. For every real $p>1$, it holds for every positive tensor power of any single-mode Gaussian channel, and for any nonempty finite family of single-mode channels whose noise matrices are positive definite and whose real determinants $\det X_i$ are identical. At $p=2$, it holds for any nonempty finite family of arbitrary multimode Gaussian channels with $\det X_i\ne0$, each acting on a positive finite number of modes. In each of these scopes,
--
--   $$\xi_p\!\left(\bigotimes_i\Phi_i\right)=\prod_i\xi_p(\Phi_i).$$
--
--   These are Gaussian-input supremum equalities and do not require a maximizing density. They isolate the three operational conclusions summarized in the abstract.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 1, Abstract/main result: Gaussian maximal-output-purity multiplicativity

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

/-- PDF p.1 abstract, pinned to the three precise proposition scopes on
pp.5--7. This aggregate asserts Gaussian-input supremum multiplicativity only. -/
theorem main_gaussian_multiplicativity :
    (∀ (E : CenteredOscillatorChannel (Fin 1)) (r : ℕ), 0 < r →
      ∀ p : ℝ, 1 < p → GaussianPurityMultiplicative p (m := fun _ : Fin r => 1) (fun _ => E)) ∧
    (∀ (r : ℕ), 0 < r → ∀ E : Fin r → CenteredOscillatorChannel (Fin 1),
      (∀ i, (E i).Y.PosDef) → (∀ i j, (E i).X.det = (E j).X.det) →
      ∀ p : ℝ, 1 < p → GaussianPurityMultiplicative p E) ∧
    (∀ (r : ℕ), 0 < r → ∀ (m : Fin r → ℕ), (∀ i, 0 < m i) →
      ∀ E : (i : Fin r) → CenteredOscillatorChannel (Fin (m i)),
      (∀ i, (E i).X.det ≠ 0) → GaussianPurityMultiplicative 2 E) := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
