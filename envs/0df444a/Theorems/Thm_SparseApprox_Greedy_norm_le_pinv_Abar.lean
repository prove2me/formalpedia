-- Prove2me | Theorems.Thm_SparseApprox_Greedy_norm_le_pinv_Abar
-- name    : SparseApprox.Greedy.norm_le_pinv_Abar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:25:20.837333+00:00
-- url     : https://prove2.me/theorems/056a81cc-3899-4358-8877-62e887dd1505
-- title:
--   Lemma 2 — $\|u^{(r)}\|_2\le\tfrac32\|\mathbf A^+\|_2\|b^{(r)}\|_2$ (with the added hypothesis that $A$ has linearly independent columns)
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\varepsilon>0$ are the input of Algorithm Greedy, and $k_0,k_1,\dots$ are the indices it selects. For $r<t$, $A^{(r)}$ (columns $a^{(r)}_j$), $b^{(r)}$ and $\tau^{(r)}$ are the columns, the vector $b$ and the set of chosen indices at the start of iteration $r$ of a run of $t$ selection iterations, as computed by the algorithm.
--
--   Assume that the columns of $A$ are linearly independent, and let $\mathbf A^+$ be the pseudo-inverse of $\mathbf A$ ($A$ with normalized columns). For $0\le r<t$, if $u^{(r)}$ is a vector with the minimum number of nonzero entries such that $\|A^{(r)}u^{(r)}-b^{(r)}\|_2\le\varepsilon/2$, then
--   $$\|u^{(r)}\|_2\le\frac32\,\|\mathbf A^+\|_2\,\|b^{(r)}\|_2 .$$
--
--   Together with Lemma 3 this bounds the quantity $\rho$ of Lemma 1 by $9\operatorname{Opt}(\varepsilon/2)\|\mathbf A^+\|_2^2$.
--
--   **Formalization Note** The hypothesis that $A$ has linearly independent columns is added; the printed Lemma 2 is false without it. Counterexample: $\mathbf A=A=[e_1,\ e_2,\ (e_1+e_2)/\sqrt2]$ has singular values $\sqrt2$ and $1$, so $\|\mathbf A^+\|_2=1$; for $b=\beta(-1,1)/\sqrt2$ and $\varepsilon\ll\beta$ no single column is within $\varepsilon/2$ of $b$, and $u^{(0)}=(-\sqrt2\beta,0,\beta)$ is a minimum-support exact solution with $\|u^{(0)}\|_2=\sqrt3\beta>\tfrac32\beta$. The proof on p. 233 needs the hypothesis at the singular-value step. The pseudo-inverse is any matrix satisfying the four Penrose equations for $\mathbf A$, and $\|\cdot\|_2$ is the spectral norm.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 232, Lemma 2 (proof pp. 232–233)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem norm_le_pinv_Abar {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε)
    (hA : LinearIndependent ℝ (colE A))
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : IsMoorePenrose (Abar A) P)
    (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u) :
    ‖u‖ ≤ 3 / 2 * opNorm2 P * ‖(greedyState A b k r).res‖ := by sorry

end SparseApprox.Greedy
