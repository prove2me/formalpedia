-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_scalar_block_reduction
-- name    : QAlgorithms.Papers.Independent.Support50.P28.scalar_block_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:14:28.331977+00:00
-- url     : https://prove2.me/theorems/16ed19c4-5d8d-449b-8c7e-207e881f1f89
-- title:
--   Lemma 2, (39)–(40): scalar-block multiplicativity reduction
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   Let $r\ge1$ and let $\Phi_i=\Phi_{X_i,Y_i}$ be single-mode Gaussian channels with equal signs of $\det X_i$, including a common zero sign. For real $p>1$, form physical canonical Gaussian channels $\widetilde\Phi_i$ with
--
--   $$\widetilde X_i=\sqrt{|\det X_i|}\,I_2,\qquad \widetilde Y_i=\sqrt{\det Y_i}\,I_2.$$
--
--   Their existence is part of the assertion. The tensor product of the original channels is multiplicative at $p$ if and only if that of these canonical channels is multiplicative at $p$.
--
--   This reduces the multiplicativity question to scalar one-mode blocks. It does not assert symplectic congruence of singular noise to zero or existence of a finite-squeezing optimizer.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 5, Lemma 2, (39)–(40): scalar-block multiplicativity reduction

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

/-- PDF p.5, Lemma 2, (39)--(40): scalar-block multiplicativity equivalence.
The canonical channels are constructed in the conclusion; neither their existence
nor any symplectic congruence of rank-one noise is assumed. Common zero signs
are included. Negative signs use global input time reversal in the source. -/
theorem scalar_block_reduction {r : ℕ} (hr : 0 < r)
    (E : Fin r → CenteredOscillatorChannel (Fin 1)) (hsign : EqualSigns E)
    (p : ℝ) (hp : 1 < p) :
    ∃ F : Fin r → CenteredOscillatorChannel (Fin 1),
      (∀ i, (F i).X = scalarX (E i) ∧ (F i).Y = scalarY (E i)) ∧
      (GaussianPurityMultiplicative p E ↔ GaussianPurityMultiplicative p F) := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
