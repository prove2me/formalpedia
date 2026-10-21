-- Prove2me | Theorems.Thm_PBElicit_RandThresh_eq_8
-- name    : PBElicit.RandThresh.eq_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:40.564468+00:00
-- url     : https://prove2.me/theorems/6e8de900-2810-4209-81d1-3bea31fec848
-- title:
--   Eq. (8), p. 13 — the greedy set B_{j,k} of Mechanism A has welfare at least (1/4)·n*_{j,k}·u_j
-- statement:
--   Let $m=2^K$ be the number of alternatives with nonnegative costs, $\vec v$ a normalized utility profile, and $S^*$ a welfare-maximizing set in $\mathcal F_c$. Fix $j,k\in\{1,\dots,2\log_2 m\}$ and let $B_{j,k}$ be any set of $\min(1/u_k,|S_k|)$ alternatives of the cost bucket $S_k$ that have the largest numbers of approval votes at threshold $\ell_j$ (ties broken arbitrarily). Then
--   $$
--   \mathrm{sw}(B_{j,k},\vec v)\ \ge\ \frac14\, n^*_{j,k}\, u_j ,
--   $$
--   where $n^*_{j,k}=\sum_{a\in S^*\cap S_k}n^a_j$.
--
--   This is the per-arm guarantee of Mechanism A: a single threshold and a single cost bucket recover a constant fraction of the welfare that $S^*$ draws from utility level $j$ in bucket $k$.
--
--   **Formalization Note.** This is the outer inequality of the page's chain (8). The page's middle inequality, with the counts $\sum_{p\ge j}n^a_p$, can fail when a voter's utility equals $\ell_j$ exactly (such a voter approves at threshold $\ell_j$ but is counted in $I_{j-1}$, since $I_j=(\ell_j,u_j]$); the outer inequality holds by the same argument with approval counts in place of those sums. `IsWelfareOptimal` pins $S^*$ to the page's optimum. $1/u_k=m^2/2^k$ is a natural number for $k\le 2K$. $m$ is `Fintype.card A` $=2^K$.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), proof of Theorem 3.5, Mechanism A and eq. (8), p. 13

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem eq_8 {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc0 : ∀ a, 0 ≤ c a) (v : Fin n → A → ℝ) (hv : IsUtilityProfile v) (m K : ℕ)
    (hA : Fintype.card A = m) (hmK : m = 2 ^ K) (Sstar : Finset A)
    (hS : IsWelfareOptimal c v Sstar)
    (j k : ℕ) (hj : j ∈ Finset.Icc 1 (2 * K)) (hk : k ∈ Finset.Icc 1 (2 * K)) (B : Finset A)
    (hB : IsGreedyTop v c m j k B) :
    (1 / 4 : ℝ) * (cntStar v c m Sstar j k : ℝ) * up m j ≤ sw v B := by sorry

end PBElicit.RandThresh
