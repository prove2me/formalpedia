-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_maximally_entangled_identities
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.maximally_entangled_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:38:56.270999+00:00
-- url     : https://prove2.me/theorems/07ec2640-a353-4b23-91ea-aca251f6e88f
-- title:
--   Lemma 1: two maximally-entangled-state identities
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Write $\Omega_d=d^{-1/2}\sum_i|ii\rangle$ and $\omega_d=|\Omega_d\rangle\langle\Omega_d|$. For every rectangular $d_2\times d_1$ matrix $X$,
--   $$(I_{d_1}\otimes X)\Omega_{d_1}=\sqrt{d_2/d_1}\,(X^T\otimes I_{d_2})\Omega_{d_2}.$$
--   For every Hermiticity-preserving map $L:M_{d_1}\to M_{d_2}$,
--   $$(\mathrm{id}_{d_1}\otimes L)(\omega_{d_1})=\frac{d_2}{d_1}\bigl((\vartheta_{d_1}\circ L^*\circ\vartheta_{d_2})\otimes\mathrm{id}_{d_2}\bigr)(\omega_{d_2}).$$
--   Here $L^*$ is the Hilbert--Schmidt adjoint. These identities retain the normalization factors for unequal local dimensions.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 4, Lemma 1: two maximally-entangled-state identities

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Lemma 1, PDF p.4: rectangular vector identity AND the Hilbert--Schmidt adjoint identity.
The normalized vector gives sqrt(d2/d1); the normalized Choi matrix gives d2/d1. -/
theorem maximally_entangled_identities [Nonempty A] [Nonempty B] :
    (∀ X : Matrix B A ℂ,
      (Matrix.kronecker (1 : Mat A) X).mulVec (WithLp.ofLp (finiteMaxEntangled A)) =
        (Real.sqrt ((Fintype.card B : ℝ) / Fintype.card A) : ℂ) •
          (Matrix.kronecker X.transpose (1 : Mat B)).mulVec (WithLp.ofLp (finiteMaxEntangled B))) ∧
    (∀ L : MatrixMap A B, (∀ X : Mat A, X.IsHermitian → (L X).IsHermitian) →
      normalizedChoi L = (((Fintype.card B : ℝ) / Fintype.card A : ℝ) : ℂ) •
        tensorLinearMap ((basisTransposeLinearMap A).comp ((hsAdjoint L).comp (basisTransposeLinearMap B)))
          (LinearMap.id : MatrixMap B B) (normalizedEntangledProjection B)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
