-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_two_way_finite_error
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.two_way_finite_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:46:52.568995+00:00
-- url     : https://prove2.me/theorems/b84ed2ea-df72-4d15-9957-704aba57cc78
-- title:
--   Lemma 4: finite-use error bound for actual two-way coding schemes
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $T:M_{d_1}\to M_{d_2}$ be a channel and let an actual sequential two-way communication scheme use $m\ge1$ calls to transmit a system of dimension $N\ge1$. Let $\epsilon=\tfrac12\|\mathrm{id}_N-\mathcal S\|_\diamond$, where $\mathcal S$ is its full input-output channel, including LOCC before, between and after all calls. Then
--   $$\epsilon\ge1-\frac{\|\vartheta_{d_2}\circ T\|_\diamond^m}{N}.$$
--   The input, memories, local maps, channel calls and final output are part of the scheme. The scalar case $N=1$ is retained.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 11, Lemma 4: finite-use error bound for actual two-way coding schemes

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

/-- Lemma 4, PDF pp.11--12: computed error of an actual sequential two-way scheme;
N=1 is allowed, and the protocol includes assistance before, between and after calls. -/
theorem two_way_finite_error (d1 d2 : ℕ) [NeZero d1] [NeZero d2]
    (T : MatrixMap (Fin d1) (Fin d2)) (hT : IsChannel T) (K : TwoPartyCode T false) :
    K.error ≥ 1 - diamond ((basisTransposeLinearMap (Fin d2)).comp T) ^ K.m / K.N := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
