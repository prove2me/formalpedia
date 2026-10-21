-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_basis_independence
-- name    : QAlgorithms.Papers.Independent.Next46.P02.basis_independence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:26:31.113995+00:00
-- url     : https://prove2.me/theorems/f3459832-7bc7-4527-b1fe-cd42f4fae05a
-- title:
--   Convergence and basis independence of square sums and positive traces
-- statement:
--   Let $H$ be a complete real or complex Hilbert space, let $T$ be a bounded endomorphism, and let $(e_i)_{i\in I}$ and $(f_j)_{j\in J}$ be arbitrary complete orthonormal bases. If either of the following nonnegative families is summable, both have a common real sum:
--
--   $$
--   \sum_{i\in I}\|Te_i\|^2=\sum_{j\in J}\|T^*f_j\|^2.
--   $$
--
--   Moreover, if the positive diagonal family $(\langle |T|e_i;e_i\rangle)_i$ is summable, its sum is the same in the second basis, and that second family is also summable:
--
--   $$
--   \sum_i\langle |T|e_i;e_i\rangle=\sum_j\langle |T|f_j;f_j\rangle.
--   $$
--
--   Here the displayed source inner product is linear in its first argument. These conclusions transfer convergence as well as numerical values and permit empty bases on the zero space.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 9, §5 opening, unnumbered basis independence of square sums and positive traces

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace F H] [CompleteSpace H]

/-- PDF p.9: basis independence transfers convergence as well as the value,
both for the square sums and for the positive modulus diagonals. -/
theorem basis_independence {I J : Type*} (b : HilbertBasis I F H)
    (c : HilbertBasis J F H) (T : H →L[F] H) :
    ((Summable (fun i => ‖T (b i)‖ ^ 2) ∨
      Summable (fun j => ‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2)) →
      ∃ r : ℝ, HasSum (fun i => ‖T (b i)‖ ^ 2) r ∧
        HasSum (fun j => ‖(ContinuousLinearMap.adjoint T) (c j)‖ ^ 2) r) ∧
    (Summable (fun i => RCLike.re (basisDiagonal b (hilbertOperatorModulus T) i)) →
      ∃ r : ℝ, HasSum (fun i => RCLike.re (basisDiagonal b (hilbertOperatorModulus T) i)) r ∧
        HasSum (fun j => RCLike.re (basisDiagonal c (hilbertOperatorModulus T) j)) r) := by sorry

end Hilbert

end QAlgorithms.Papers.Independent.Next46.P02

end
