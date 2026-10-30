-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_block_positive_twirls
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.block_positive_twirls
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:59:07.520134+00:00
-- url     : https://prove2.me/theorems/7f90d6b7-920e-45fd-8cd6-8393011130f2
-- title:
--   Lemma 9: positivity of both twirls for appropriate block-positive inputs
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $d\ge1$ and let $C\in M_d\otimes M_d$ be Hermitian and block-positive. With normalized Haar measure on $\mathcal U(d)$,
--   $$\operatorname{tr}(CF_d)\le0\ \Longrightarrow\ \int(U\otimes U)C(U\otimes U)^\dagger\,dU\ge0,$$
--   $$\operatorname{tr}(C\omega_d)\ge0\ \Longrightarrow\ \int(U\otimes\overline U)C(U\otimes\overline U)^\dagger\,dU\ge0.$$
--   Here $F_d|ij\rangle=|ji\rangle$. The second factor is entrywise conjugate $U$, not its adjoint. Both continuous compact-group integrands are integrable; block positivity includes Hermiticity.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 23, Lemma 9: positivity of both twirls for appropriate block-positive inputs

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

/-- Lemma 9, PDF pp.23--24: both twirls with their distinct trace tests.
Every positive dimension is included; at d=1 both twirls are the identity. -/
theorem block_positive_twirls (d : ℕ) [NeZero d]
    (C : Mat (Fin d × Fin d)) (hC : ProductBlockPositive C) :
    ((C * (swapMatrix (I := Fin d))).trace.re ≤ 0 → (bipartiteHaarTwirl d false C).PosSemidef) ∧
    (0 ≤ (C * normalizedEntangledProjection (Fin d)).trace.re → (bipartiteHaarTwirl d true C).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
