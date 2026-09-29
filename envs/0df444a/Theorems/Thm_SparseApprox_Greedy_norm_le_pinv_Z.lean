-- Prove2me | Theorems.Thm_SparseApprox_Greedy_norm_le_pinv_Z
-- name    : SparseApprox.Greedy.norm_le_pinv_Z
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:24:13.877435+00:00
-- url     : https://prove2.me/theorems/c76fdd44-ec39-424f-9144-d3f526b5d9d0
-- title:
--   Eq. (31) — $\|u^{(r)}\|_2\le \tfrac32\|Z^+\|_2\|b^{(r)}\|_2$
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\varepsilon>0$ are the input of Algorithm Greedy, and $k_0,k_1,\dots$ are the indices it selects. For $r<t$, $A^{(r)}$ (columns $a^{(r)}_j$), $b^{(r)}$ and $\tau^{(r)}$ are the columns, the vector $b$ and the set of chosen indices at the start of iteration $r$ of a run of $t$ selection iterations, as computed by the algorithm.
--
--   Let $r<t$, let $u^{(r)}$ be a vector with the minimum number of nonzero entries such that $\|A^{(r)}u^{(r)}-b^{(r)}\|_2\le\varepsilon/2$, let $\sigma=\{i : u^{(r)}_i\neq0\}$ and $\tau=\{k_0,\dots,k_{r-1}\}$. Let $Z$ be the $m\times|\sigma\cup\tau|$ matrix with columns $a^{(0)}_i$, $i\in\sigma\cup\tau$ (columns of $\mathbf A$), and $Z^+$ its pseudo-inverse. Then
--   $$\|u^{(r)}\|_2\le\frac32\,\|Z^+\|_2\,\|b^{(r)}\|_2 .$$
--
--   This is the content of Lemma 2 that holds for every matrix $A$; Lemma 2 itself then compares $\|Z^+\|_2$ with $\|\mathbf A^+\|_2$.
--
--   **Formalization Note** $Z^+$ is given as any matrix satisfying the four Penrose equations for $Z$ (it is unique), and $\|\cdot\|_2$ is the $\ell_2\to\ell_2$ operator norm.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 233, Eq. (31) (with (29)–(30), proof of Lemma 2)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem norm_le_pinv_Z {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (PZ : Matrix ↥(nzSet u ∪ (greedyState A b k r).chosen) (Fin m) ℝ)
    (hPZ : IsMoorePenrose
      (colsMatrix (fun i : ↥(nzSet u ∪ (greedyState A b k r).chosen) => (initState A b).col i))
      PZ) :
    ‖u‖ ≤ 3 / 2 * opNorm2 PZ * ‖(greedyState A b k r).res‖ := by sorry

end SparseApprox.Greedy
