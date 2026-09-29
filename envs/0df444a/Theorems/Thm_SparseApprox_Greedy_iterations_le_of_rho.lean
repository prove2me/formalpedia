-- Prove2me | Theorems.Thm_SparseApprox_Greedy_iterations_le_of_rho
-- name    : SparseApprox.Greedy.iterations_le_of_rho
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:22:09.149351+00:00
-- url     : https://prove2.me/theorems/f7a94de4-8fd4-4478-b3a3-98d0e14206e3
-- title:
--   Lemma 1 — the selection phase runs at most $\lceil 2\rho\ln(\|b\|_2/\varepsilon)\rceil$ iterations
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\varepsilon>0$ are the input of Algorithm Greedy, and $k_0,k_1,\dots$ are the indices it selects. For $r<t$, $A^{(r)}$ (columns $a^{(r)}_j$), $b^{(r)}$ and $\tau^{(r)}$ are the columns, the vector $b$ and the set of chosen indices at the start of iteration $r$ of a run of $t$ selection iterations, as computed by the algorithm.
--
--   For each $r<t$ let $u^{(r)}$ be a vector with the minimum number $N^{(r)}$ of nonzero entries such that $\|A^{(r)}u^{(r)}-b^{(r)}\|_2\le\varepsilon/2$, and let $\rho$ be a real number bounding every term of the paper's definition (2),
--   $$4\,N^{(r)}\,\|u^{(r)}\|_2^2\le\rho\,\|b^{(r)}\|_2^2\qquad(0\le r<t).$$
--   Then the number of iterations satisfies
--   $$t\le\Big\lceil 2\rho\ln\Big(\frac{\|b\|_2}{\varepsilon}\Big)\Big\rceil .$$
--
--   This is the first of the three lemmas that combine into Theorem 2: it bounds the number of selected columns by $\rho$, and Lemmas 2 and 3 then bound $\rho$.
--
--   **Formalization Note** "Every $\rho$ bounding each term of (2)" is used instead of the maximum in (2); the bound is monotone in $\rho$ whenever $t\ge1$, so the two readings agree, and the form avoids a maximum over an empty range at $t=0$. The ceiling is the natural-number ceiling `Nat.ceil`, which agrees with the integer ceiling whenever $t\ge1$ (then $\|b\|_2>\varepsilon$ and the logarithm is positive). No condition $\rho>1$ is assumed: at $\rho=1$ the statement remains true although the paper's (21) takes $\ln(1-1/\rho)$. The hypotheses can hold only if a vector $x$ with $\|Ax-b\|_2\le\varepsilon/2$ exists.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 230, Lemma 1, Eq. (3) (proof pp. 230–232, (4)–(23))

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem iterations_le_of_rho {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (u : ℕ → EuclideanSpace ℝ (Fin n))
    (hu : ∀ r < t,
      IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) (u r))
    (ρ : ℝ)
    (hρ : ∀ r < t, 4 * (nnz (u r) : ℝ) * ‖u r‖ ^ 2 ≤ ρ * ‖(greedyState A b k r).res‖ ^ 2) :
    t ≤ ⌈2 * ρ * Real.log (‖b‖ / ε)⌉₊ := by sorry

end SparseApprox.Greedy
