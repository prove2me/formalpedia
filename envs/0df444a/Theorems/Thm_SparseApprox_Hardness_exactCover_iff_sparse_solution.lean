-- Prove2me | Theorems.Thm_SparseApprox_Hardness_exactCover_iff_sparse_solution
-- name    : SparseApprox.Hardness.exactCover_iff_sparse_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:28:52.352601+00:00
-- url     : https://prove2.me/theorems/2bf9f746-8ed7-49aa-9126-aa0fc4d37741
-- title:
--   Theorem 1 (reduction) — C has an exact cover iff Ax = 1 has a 1/2-approximate solution with at most m/3 nonzeros
-- statement:
--   Let $S=\{s_1,\dots,s_m\}$ and let $C=c_1,\dots,c_n$ be a list of 3-element subsets of $S$ (an instance of Exact Cover by 3-sets). Let $A\in\mathbb R^{m\times n}$ be the incidence matrix of $C$, with $A_{ij}=1$ if $s_i\in c_j$ and $A_{ij}=0$ otherwise, and let $b=(1,1,\dots,1)\in\mathbb R^m$. Then $C$ contains an exact cover of $S$ — a sub-collection in which every element of $S$ occurs exactly once — if and only if there is $x\in\mathbb R^n$ with
--
--   $$\|Ax-b\|_2\le\tfrac12\qquad\text{and}\qquad \|x\|_0\le\tfrac m3,$$
--
--   where $\|x\|_0$ is the number of nonzero entries of $x$.
--
--   In words: the instance $(A,b,\varepsilon=1/2)$ of the sparse approximate solution problem has a solution with $m/3$ or fewer nonzero entries exactly when the X3C instance is a yes-instance. This equivalence is the mathematical content of Natarajan's proof that the sparse approximate solution problem is NP-hard: the transformation from X3C is an $m\times n$ $0/1$ matrix and is evidently polynomial-time computable.
--
--   **Formalization Note** Only the correctness of the transformation is formalized. The machine model (the infinite-precision RAM), polynomial-time reductions and the NP-completeness of X3C (cited by the paper from Garey–Johnson) are not. "$m/3$ or fewer" is written $3\|x\|_0\le m$; with this form the equivalence holds for every $m$, both sides being false when $3\nmid m$, which absorbs the paper's "without loss of generality $m$ is a multiple of 3" — no divisibility hypothesis is assumed. The collection is indexed, so repeated sets are allowed and counted per index on both sides. The norm is the Euclidean norm of `EuclideanSpace ℝ (Fin m)`.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 228, Theorem 1 and its proof ("We show that the constructed instance of SAS has a solution with m/3 or fewer entries if and only if the given instance of X3C has a solution")

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

namespace SparseApprox.Hardness

theorem exactCover_iff_sparse_solution {m n : ℕ} (C : Fin n → Finset (Fin m))
    (hC : ∀ j, (C j).card = 3) :
    (∃ J : Finset (Fin n), IsExactCover C J) ↔
      ∃ x : EuclideanSpace ℝ (Fin n),
        ‖Matrix.toEuclideanLin (incidence C) x - onesVec m‖ ≤ 1 / 2 ∧ 3 * nnz x ≤ m := by sorry

end SparseApprox.Hardness
