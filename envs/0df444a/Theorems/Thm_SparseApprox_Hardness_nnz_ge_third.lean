-- Prove2me | Theorems.Thm_SparseApprox_Hardness_nnz_ge_third
-- name    : SparseApprox.Hardness.nnz_ge_third
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:27:49.237863+00:00
-- url     : https://prove2.me/theorems/b4b37036-d449-4132-8c99-65c85db56f14
-- title:
--   Theorem 1, proof (converse, second step) — a 1/2-approximate solution has at least m/3 nonzeros
-- statement:
--   Let $C=c_1,\dots,c_n$ be a list of 3-element subsets of $S=\{s_1,\dots,s_m\}$, let $A\in\mathbb R^{m\times n}$ be its incidence matrix and $b=(1,\dots,1)\in\mathbb R^m$. Every $x\in\mathbb R^n$ with $\|Ax-b\|_2\le 1/2$ has at least $m/3$ nonzero entries:
--
--   $$m\le 3\,\|x\|_0 .$$
--
--   This is the step "since each column of $A$ has only three nonzero entries, $x$ must have at least $m/3$ entries" of the proof of Theorem 1; combined with the sparsity assumption it shows that $x$ has exactly $m/3$ nonzero entries.
--
--   **Formalization Note** "At least $m/3$" is written multiplicatively, $m\le 3\|x\|_0$, to avoid natural-number division. The hypothesis that every $c_j$ has exactly $3$ elements is the paper's "3-element subsets".
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 228, proof of Theorem 1, last paragraph, second sentence ("Since each column of A has only three nonzero entries, x must have at least m/3 entries")

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

namespace SparseApprox.Hardness

theorem nnz_ge_third {m n : ℕ} (C : Fin n → Finset (Fin m))
    (hC : ∀ j, (C j).card = 3) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖Matrix.toEuclideanLin (incidence C) x - onesVec m‖ ≤ 1 / 2) :
    m ≤ 3 * nnz x := by sorry

end SparseApprox.Hardness
