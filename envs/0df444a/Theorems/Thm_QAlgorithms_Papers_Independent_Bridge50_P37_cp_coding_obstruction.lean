-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_cp_coding_obstruction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.cp_coding_obstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:51:41.008118+00:00
-- url     : https://prove2.me/theorems/68b9d02a-df6d-4723-808d-7a4104c7ba85
-- title:
--   Corollary 1: coding-scheme obstruction to complete-positivity distance
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $n\ge1$ and let $P:M_{d_1}\to M_{d_2}$ be nonzero and $n$-tensor-stable positive. Then
--   $$\frac{d_{\rm CP}(P)}{\|P\|_\diamond}\le\inf_{m\ge1,\,E_i,D_i\ {\rm CP}}\left\|\mathrm{id}_{d_1}-\sum_{i=1}^m D_i\circ P^{\otimes(n-1)}\circ E_i\right\|_\diamond.$$
--   Here $E_i:M_{d_1}\to M_{d_1}^{\otimes(n-1)}$ and $D_i:M_{d_2}^{\otimes(n-1)}\to M_{d_1}$ are arbitrary CP maps, without trace-preservation or contraction assumptions. At $n=1$ the zero-copy algebras are scalar. The distance $d_{\rm CP}$ is the negative spectral mass of the normalized Choi matrix.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 15, Corollary 1: coding-scheme obstruction to complete-positivity distance

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

/-- Corollary 1, PDF p.15: n>=1, P nonzero, arbitrary finite sums of CP encoders and decoders. -/
theorem cp_coding_obstruction [Nonempty A] [Nonempty B] (P : MatrixMap A B)
    (n : ℕ) (hP : NTensorStable P n) (hne : P ≠ 0) :
    distanceCP P / diamond P ≤ sInf (cpCodingErrors P (n-1)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
