-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_theorem_6_9_order4
-- name    : TensorNP.SpectralNorm.theorem_6_9_order4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:53.122197+00:00
-- url     : https://prove2.me/theorems/3a169e29-18dd-40db-a1dd-07f95f60b55e
-- title:
--   Theorem 6.9 (Banach), identity (24) — the spectral norm of a symmetric 4-tensor is attained on the diagonal
-- statement:
--   Let $\mathcal S\in\mathbb R^{n\times n\times n\times n}$ be a symmetric 4-tensor, i.e. $s_{ijkp}$ is invariant under every permutation of the indices. Then
--   $$
--   \|\mathcal S\|_{2,2,2,2}=\sup_{\mathbf w,\mathbf x,\mathbf y,\mathbf z\neq\mathbf 0}\frac{|\mathcal S(\mathbf w,\mathbf x,\mathbf y,\mathbf z)|}{\|\mathbf w\|_2\|\mathbf x\|_2\|\mathbf y\|_2\|\mathbf z\|_2}=\sup_{\mathbf x\neq\mathbf 0}\frac{|\mathcal S(\mathbf x,\mathbf x,\mathbf x,\mathbf x)|}{\|\mathbf x\|_2^4}. \tag{24}
--   $$
--
--   This is the order-4 case of Banach's theorem (1938): the spectral norm of a symmetric tensor can be computed from its homogeneous polynomial alone.
--
--   **Formalization Note** The first equality in (24) is the definition `specNorm4`; the theorem asserts the second. Both suprema are `sSup` of sets of quotients over nonzero vectors (for $n=0$ both sets are empty and both sides are $0$). Symmetry is invariance under the three adjacent index transpositions, which generate all permutations. The order-3 identity (23) is not part of this item.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:23, Theorem 6.9 (Banach 1938), (24)

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor

namespace TensorNP.SpectralNorm

/-- **Theorem 6.9 (Banach), identity (24).** For a symmetric real 4-tensor
`S ∈ ℝ^{n×n×n×n}`, `‖S‖_{2,2,2,2} = sup_{x ≠ 0} |S(x,x,x,x)| / ‖x‖₂⁴`. -/
theorem theorem_6_9_order4 {n : ℕ} (S : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hS : IsSymmetric4 S) :
    specNorm4 S =
      sSup {t : ℝ | ∃ x : Fin n → ℝ, x ≠ 0 ∧ t = |quadrilinear S x x x x| / l2norm x ^ 4} := by sorry

end TensorNP.SpectralNorm
