-- Prove2me | Theorems.Thm_PBElicit_RandThresh_mechanism_A_bound
-- name    : PBElicit.RandThresh.mechanism_A_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:31.877686+00:00
-- url     : https://prove2.me/theorems/0025d19f-e491-40c0-98ea-07bd1879f1d3
-- title:
--   Proof of Theorem 3.5, p. 13 — Mechanism A's expected welfare is at least (sw(S* \ S_0, v⃗) − n/m)/(16 log² m)
-- statement:
--   Let $m=2^K$ with $K\ge 1$ be the number of alternatives with nonnegative costs, $\vec v$ a normalized utility profile of $n$ voters, and $S^*$ a welfare-maximizing set in $\mathcal F_c$. For each pair $(j,k)\in[2\log m]^2$ let $B_{j,k}$ be a greedy set of Mechanism A (the $\min(1/u_k,|S_k|)$ alternatives of $S_k$ with the most approvals at threshold $\ell_j$). Then
--   $$
--   \frac{1}{(2\log m)^2}\sum_{j=1}^{2\log m}\sum_{k=1}^{2\log m}\mathrm{sw}(B_{j,k},\vec v)\ \ge\ \frac{1}{16\log^2 m}\Big(\mathrm{sw}(S^*\setminus S_0,\vec v)-\frac nm\Big).
--   $$
--   The left side is the expected welfare of Mechanism A, which picks $(j,k)$ uniformly at random.
--
--   **Formalization Note.** This is the first and last term of the page's chain; the intermediate terms are the proof. $\log$ is $\log_2$, so $\log m=K$; the constants $1/(2\log m)^2$ and $1/(16\log^2 m)$ are kept as printed. `IsWelfareOptimal` pins $S^*$ to the page's optimum.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), proof of Theorem 3.5, display after eq. (8), pp. 13–14

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem mechanism_A_bound {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (hc0 : ∀ a, 0 ≤ c a) (v : Fin n → A → ℝ) (hv : IsUtilityProfile v) (m K : ℕ) (hK : 1 ≤ K)
    (hA : Fintype.card A = m) (hmK : m = 2 ^ K) (Sstar : Finset A)
    (hS : IsWelfareOptimal c v Sstar)
    (B : ℕ → ℕ → Finset A)
    (hB : ∀ j ∈ Finset.Icc 1 (2 * K), ∀ k ∈ Finset.Icc 1 (2 * K), IsGreedyTop v c m j k (B j k)) :
    1 / (16 * Real.logb 2 m ^ 2) * (sw v (Sstar \ bucket c m 0) - (n : ℝ) / m)
      ≤ 1 / (2 * Real.logb 2 m) ^ 2 *
          ∑ j ∈ Finset.Icc 1 (2 * K), ∑ k ∈ Finset.Icc 1 (2 * K), sw v (B j k) := by sorry

end PBElicit.RandThresh
