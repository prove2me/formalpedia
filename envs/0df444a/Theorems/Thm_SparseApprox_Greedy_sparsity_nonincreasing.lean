-- Prove2me | Theorems.Thm_SparseApprox_Greedy_sparsity_nonincreasing
-- name    : SparseApprox.Greedy.sparsity_nonincreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:22:39.126419+00:00
-- url     : https://prove2.me/theorems/3f6877cc-add8-4f4f-a89d-f9e1543ee8f3
-- title:
--   Lemma 3 — $N^{(r+1)}\le N^{(r)}\le N^{(0)}$
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\varepsilon>0$ are the input of Algorithm Greedy, and $k_0,k_1,\dots$ are the indices it selects. For $r<t$, $A^{(r)}$ (columns $a^{(r)}_j$), $b^{(r)}$ and $\tau^{(r)}$ are the columns, the vector $b$ and the set of chosen indices at the start of iteration $r$ of a run of $t$ selection iterations, as computed by the algorithm.
--
--   For $s\le t$ let $N^{(s)}$ be the minimum number of nonzero entries of a vector $u$ with $\|A^{(s)}u-b^{(s)}\|_2\le\varepsilon/2$. The number of entries in the sparse solution is nonincreasing as the algorithm iterates: for $r<t$, if $u^{(0)}$, $u^{(r)}$ and $u^{(r+1)}$ are minimum-support vectors at iterations $0$, $r$ and $r+1$, then
--   $$N^{(r+1)}\le N^{(r)}\le N^{(0)} .$$
--
--   Combined with $N^{(0)}=\operatorname{Opt}(\varepsilon/2)$, this replaces $N^{(r)}$ by $\operatorname{Opt}(\varepsilon/2)$ in the definition (2) of $\rho$.
--
--   **Formalization Note** $N^{(s)}$ is represented through minimum-support vectors (`IsMinSparseSol`), whose number of nonzero entries is the minimum. Iteration $r+1$ is the state produced by the $r$-th greedy step of the run.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 233, Lemma 3

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem sparsity_nonincreasing {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t)
    (u₀ u u' : EuclideanSpace ℝ (Fin n))
    (hu₀ : IsMinSparseSol (greedyState A b k 0).col (greedyState A b k 0).res (ε / 2) u₀)
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (hu' : IsMinSparseSol (greedyState A b k (r + 1)).col (greedyState A b k (r + 1)).res
      (ε / 2) u') :
    nnz u' ≤ nnz u ∧ nnz u ≤ nnz u₀ := by sorry

end SparseApprox.Greedy
