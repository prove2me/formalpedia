-- Prove2me | Theorems.Thm_SparseApprox_Hardness_support_isExactCover
-- name    : SparseApprox.Hardness.support_isExactCover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:28:29.651747+00:00
-- url     : https://prove2.me/theorems/60484c92-dbb6-4d88-a299-bf5634f62f56
-- title:
--   Theorem 1, proof (converse, conclusion) — the sets c_j with x_j ≠ 0 form an exact cover
-- statement:
--   Let $C=c_1,\dots,c_n$ be a list of 3-element subsets of $S=\{s_1,\dots,s_m\}$, let $A\in\mathbb R^{m\times n}$ be its incidence matrix and $b=(1,\dots,1)\in\mathbb R^m$. Suppose $x\in\mathbb R^n$ satisfies
--
--   $$\|Ax-b\|_2\le\tfrac12\qquad\text{and}\qquad 3\,\|x\|_0\le m .$$
--
--   Then the sub-collection $\hat C=\{c_j : x_j\neq 0\}$ is an exact cover of $S$: every element of $S$ lies in exactly one set $c_j$ with $x_j\neq0$.
--
--   This is the conclusion of the converse direction of the proof of Theorem 1: a sparse approximate solution of the constructed SAS instance yields an exact cover.
--
--   **Formalization Note** "At most $m/3$ nonzero entries" is written $3\|x\|_0\le m$, avoiding natural-number division. $\hat C$ is given by its index set $\{j : x_j\neq0\}$, so repeated sets in $C$ are distinct indices.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 228, proof of Theorem 1, last paragraph, last two sentences ("Now consider the subcollection Ĉ … It is clear that Ĉ is an exact cover for S")

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

namespace SparseApprox.Hardness

theorem support_isExactCover {m n : ℕ} (C : Fin n → Finset (Fin m))
    (hC : ∀ j, (C j).card = 3) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖Matrix.toEuclideanLin (incidence C) x - onesVec m‖ ≤ 1 / 2)
    (hsparse : 3 * nnz x ≤ m) :
    IsExactCover C (Finset.univ.filter (fun j => x j ≠ 0)) := by sorry

end SparseApprox.Hardness
