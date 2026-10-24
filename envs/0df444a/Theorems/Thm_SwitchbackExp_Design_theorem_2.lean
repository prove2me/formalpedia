-- Prove2me | Theorems.Thm_SwitchbackExp_Design_theorem_2
-- name    : SwitchbackExp.Design.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:55.127069+00:00
-- url     : https://prove2.me/theorems/40d6b68f-18e9-442c-b673-f63ea86c7d63
-- title:
--   Theorem 2, p. 13 — for m = 0 the unique minimax-optimal regular design is 𝕋* = [T]; for T = nm, m ≥ 1, n ≥ 4 it is 𝕋* = {1, 2m+1, …, (n−2)m+1}; both with fair coins
-- statement:
--   Let $B>0$ and consider regular switchback designs under Assumptions 1–3 with bound $B$, with estimand and estimator of lag $m$.
--
--   1. If $m=0$ and $T\ge2$, the regular design with randomization points $\mathbb T^*=\{1,2,3,\dots,T\}$ and fair coins solves the minimax problem
--   $$\min_{\mathbb T\subseteq[T],\,\mathbb Q}\ \max_{\mathbb Y\in\mathcal Y}\ r(\eta_{\mathbb T,\mathbb Q},\mathbb Y),\qquad(6)$$
--   and every solution of (6) has $\mathbb T=\mathbb T^*$ and $q_0=\dots=q_K=1/2$.
--   2. If $m\ge1$ and $T=nm$ for an integer $n\ge4$, the regular design with
--   $$\mathbb T^*=\{1,\ 2m+1,\ 3m+1,\ \dots,\ (n-2)m+1\}$$
--   and fair coins solves (6), and every solution of (6) has $\mathbb T=\mathbb T^*$ and $q_0=\dots=q_K=1/2$.
--
--   The optimal design randomizes once every $m$ periods, except for the first and the last epoch, which last $2m$ periods each; the optimal randomization frequency depends on the physical duration of the carryover effect.
--
--   **Formalization Note** The statement combines Theorem 2's closed form with Theorem 1's fair coins, and asserts both existence and uniqueness of the optimum ("*the* optimal solution"). The comparison class in (6) is every regular design $(\mathbb T',\mathbb Q')$ with $q\in(0,1)$, not only fair-coin designs. $T\ge2$ in the case $m=0$ is the page's requirement that $K$ be a positive integer: $\mathbb T^*=[T]$ has $K=T-1$. The first sentence of Theorem 2 (equivalence of (6) with (7)) is a separate item, because as printed it fails for short horizons.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Theorem 2, p. 13 (with Theorem 1, p. 12); proof EC.3.6.1, pp. ec21–ec23

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Theorem 2 (p. 13), closed form, with Theorem 1: for `m = 0` (and `T ≥ 2`) the unique minimax-optimal
regular design is `𝕋* = [T]` with fair coins; for `m ≥ 1` and `T = n m`, `n ≥ 4`, it is
`𝕋* = {1, 2m+1, 3m+1, …, (n−2)m+1}` with fair coins. -/
theorem theorem_2 (m T : ℕ) (B : ℝ) (hB : 0 < B) :
    (m = 0 → 2 ≤ T →
      IsMinimaxOptimal 0 T B (Finset.Icc 1 T) half ∧
      ∀ (P : Finset ℕ) (q : ℕ → ℝ), IsMinimaxOptimal 0 T B P q →
        P = Finset.Icc 1 T ∧ ∀ t ∈ P, q t = 1 / 2) ∧
    (∀ n : ℕ, 1 ≤ m → 4 ≤ n → T = n * m →
      IsMinimaxOptimal m T B (optPoints m n) half ∧
      ∀ (P : Finset ℕ) (q : ℕ → ℝ), IsMinimaxOptimal m T B P q →
        P = optPoints m n ∧ ∀ t ∈ P, q t = 1 / 2) := by sorry

end SwitchbackExp.Design
