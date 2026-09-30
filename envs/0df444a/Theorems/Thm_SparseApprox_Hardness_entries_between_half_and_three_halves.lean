-- Prove2me | Theorems.Thm_SparseApprox_Hardness_entries_between_half_and_three_halves
-- name    : SparseApprox.Hardness.entries_between_half_and_three_halves
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:27:18.808793+00:00
-- url     : https://prove2.me/theorems/bca0ec93-e811-4937-8566-ab97bc41e1ef
-- title:
--   Theorem 1, proof (converse, first step) — ‖Ax − b‖₂ ≤ 1/2 forces every entry of Ax into [1/2, 3/2]
-- statement:
--   Let $C=c_1,\dots,c_n$ be a list of subsets of $S=\{s_1,\dots,s_m\}$, let $A\in\mathbb R^{m\times n}$ be its incidence matrix and $b=(1,\dots,1)\in\mathbb R^m$. For every $x\in\mathbb R^n$ with $\|Ax-b\|_2\le 1/2$ and every row $i$,
--
--   $$\tfrac12\le (Ax)_i\le\tfrac32 .$$
--
--   In particular every entry of $Ax$ is nonzero, so every element $s_i$ lies in some set $c_j$ with $x_j\neq0$. This is the first step of the converse direction in the proof of Theorem 1.
--
--   **Formalization Note** The statement holds for every $x$, with no sparsity assumption and no condition on the sizes of the sets; $\|\cdot\|_2$ is the Euclidean norm on `EuclideanSpace ℝ (Fin m)`.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 228, proof of Theorem 1, last paragraph, first sentence ("Since ‖Ax − b‖₂ ≤ 1/2, each entry of Ax must be between 1/2 and 3/2")

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

namespace SparseApprox.Hardness

theorem entries_between_half_and_three_halves {m n : ℕ} (C : Fin n → Finset (Fin m))
    (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖Matrix.toEuclideanLin (incidence C) x - onesVec m‖ ≤ 1 / 2) (i : Fin m) :
    1 / 2 ≤ Matrix.toEuclideanLin (incidence C) x i ∧
      Matrix.toEuclideanLin (incidence C) x i ≤ 3 / 2 := by sorry

end SparseApprox.Hardness
