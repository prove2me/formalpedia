-- Prove2me | Theorems.Thm_StochGradTrack_Dimin_sum_bounds
-- name    : StochGradTrack.Dimin.sum_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:55.186353+00:00
-- url     : https://prove2.me/theorems/4559d902-07dc-4797-bd78-c240dc135825
-- title:
--   p. 427 — Σ(m+t)^{θμ−3} ≤ max{(m+k)^{θμ−2}/(θμ−2), (m−1)^{θμ−2}/(2−θμ)} and Σ(m+t)^{θμ−2} ≤ (m+k)^{θμ−1}/(θμ−1)
-- statement:
--   Let $m>1$ and $\theta\mu>1$. For every $k\ge0$,
--   $$\sum_{t=0}^{k-1}(m+t)^{\theta\mu-2}\le\frac1{\theta\mu-1}(m+k)^{\theta\mu-1},$$
--   and, if $\theta\mu\ne2$,
--   $$\sum_{t=0}^{k-1}(m+t)^{\theta\mu-3}\le\max\Big\{\frac1{\theta\mu-2}(m+k)^{\theta\mu-2},\;\frac1{2-\theta\mu}(m-1)^{\theta\mu-2}\Big\}.$$
--
--   These comparisons of sums with integrals $\int_{-1}^k(m+t)^{s}\,dt$ give the final rate of $U_k$ in Theorem 2.
--
--   **Formalization Note** The page states the first bound without excluding $\theta\mu=2$, where both branches of the maximum involve $1/0$ (the true bound is logarithmic); the hypothesis $\theta\mu\ne2$ is added for that bound. The intermediate integrals of the page are not stated. Powers are real powers.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.3, p. 427 ("Note that" display)

import Mathlib

namespace StochGradTrack.Dimin

/-- The sum–integral bounds (p. 427), for `m > 1` and `θμ > 1`; the first one (disclosed) for `θμ ≠ 2`. -/
theorem sum_bounds (θ μ m : ℝ) (hm : 1 < m) (hθμ : 1 < θ * μ) (k : ℕ) :
    (θ * μ ≠ 2 →
      ∑ t ∈ Finset.range k, (m + t) ^ (θ * μ - 3)
        ≤ max (1 / (θ * μ - 2) * (m + k) ^ (θ * μ - 2)) (1 / (2 - θ * μ) * (m - 1) ^ (θ * μ - 2))) ∧
    ∑ t ∈ Finset.range k, (m + t) ^ (θ * μ - 2) ≤ 1 / (θ * μ - 1) * (m + k) ^ (θ * μ - 1) := by sorry

end StochGradTrack.Dimin
