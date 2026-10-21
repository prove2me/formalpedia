-- Prove2me | Theorems.Thm_PBElicit_RandThresh_eq_7
-- name    : PBElicit.RandThresh.eq_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:50:13.470355+00:00
-- url     : https://prove2.me/theorems/91ab87a0-a9c2-484b-8ffe-85ffd09ad8e2
-- title:
--   Eq. (7), p. 13 — the welfare of S* ∩ S_k is sandwiched by the counts n*_{j,k}
-- statement:
--   Let $m=2^K$ be the number of alternatives, $\vec v$ a normalized utility profile of $n$ voters, $S^*$ a welfare-maximizing set in $\mathcal F_c$, and $k\in\{0,\dots,2K\}$ a bucket index. With $n^*_{j,k}=\sum_{a\in S^*\cap S_k}n^a_j$ and $\ell_j,u_j$ as in (6),
--   $$
--   \sum_{j=1}^{2\log m} n^*_{j,k}\,\ell_j\ \le\ \mathrm{sw}(S^*\cap S_k,\vec v)\ \le\ |S^*\cap S_k|\cdot\frac{n}{m^2}+\sum_{j=1}^{2\log m} n^*_{j,k}\,u_j .
--   $$
--   It aggregates (6) over the part of the optimal set lying in one cost bucket.
--
--   **Formalization Note.** `IsWelfareOptimal c v Sstar` states the page's choice of $S^*$ as an optimal member of $\mathcal F_c$. $m$ is `Fintype.card A` $=2^K$, logarithms base $2$.
-- source:
--   Benadè, Nath, Procaccia & Shah, Preference Elicitation for Participatory Budgeting, author's manuscript (2018; Manag. Sci. 2021, doi:10.1287/mnsc.2020.3666), proof of Theorem 3.5, eq. (7), p. 13

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

namespace PBElicit.RandThresh

theorem eq_7 {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A] (c : A → ℝ)
    (v : Fin n → A → ℝ) (hv : IsUtilityProfile v) (m K : ℕ) (hA : Fintype.card A = m)
    (hmK : m = 2 ^ K) (Sstar : Finset A) (hS : IsWelfareOptimal c v Sstar)
    (k : ℕ) (hk : k ≤ 2 * K) :
    ∑ j ∈ Finset.Icc 1 (2 * K), (cntStar v c m Sstar j k : ℝ) * lo m j
        ≤ sw v (Sstar ∩ bucket c m k) ∧
      sw v (Sstar ∩ bucket c m k)
        ≤ ((Sstar ∩ bucket c m k).card : ℝ) * ((n : ℝ) / (m : ℝ) ^ 2)
          + ∑ j ∈ Finset.Icc 1 (2 * K), (cntStar v c m Sstar j k : ℝ) * up m j := by sorry

end PBElicit.RandThresh
