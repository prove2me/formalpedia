-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_appB_sqrt_count_bound
-- name    : PosteriorSamplingRL.Regret.appB_sqrt_count_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:07:42.619317+00:00
-- url     : https://prove2.me/theorems/17a55533-a925-48cd-a341-554030e842d0
-- title:
--   App. B, p. 10 — Σ_k Σ_i √(1(N_{t_k} > τ)/N_{t_k}) ≤ √(8SAmτ) (corrected from √(2SAT))
-- statement:
--   Let $(s_{k,i},a_{k,i})$ be any sequence of state–action pairs as above, with visit counts $N_{t_k}(s,a)$ before episode $k$, and write $N_{k,i}=N_{t_k}(s_{k,i},a_{k,i})$. Then for every number of episodes $m$, with $T=m\tau$ steps,
--   $$
--   \sum_{k=1}^m\sum_{i=1}^\tau\sqrt{\frac{\mathbf 1(N_{k,i}>\tau)}{N_{k,i}}}\le\sqrt{8SA\,m\tau}.
--   $$
--
--   With the small-count bound, this controls $\sum_k\sum_i\min\{\beta_k(s_{k,i},a_{k,i}),1\}$ and yields the $\sqrt{T}$ rate of Theorem 1.
--
--   **Formalization Note** The page prints $\sqrt{2SAT}$, which is false: its chain bounds $\sum_{j=1}^N j^{-1/2}$ by $\int_0^N x^{-1/2}dx$ and then uses $\sqrt N$, while the integral equals $2\sqrt N$. With one state–action pair and $\tau=1$ the left side is about $2\sqrt T$, e.g. $17.4>14.1=\sqrt{2\cdot100}$ at $T=100$. Correcting the integral in the page's own chain gives $\sqrt2\sum_{s,a}2\sqrt{N_{T+1}(s,a)}\le\sqrt{8SAT}$, which is stated. The statement is deterministic.
-- source:
--   arXiv:1306.0940v5, App. B, p. 10, square-root sum

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Confidence

namespace PosteriorSamplingRL.Regret

/-- App. B (arXiv:1306.0940v5, p. 10), the square-root sum, with the page's `√(2SAT)` corrected
to `√(8SAT)`, `T = mτ`: for any sequence of state–action pairs (episode `k`, step `j`),
`∑_{k=1}^m ∑_{i=1}^τ √(1(N_{t_k} > τ) / N_{t_k}) ≤ √(8 S A m τ)`, where
`N_{t_k} = N_{t_k}(s_{k,i}, a_{k,i})`. -/
theorem appB_sqrt_count_bound (S A τ : ℕ) (sa : ℕ → Fin τ → Fin S × Fin A) (m : ℕ) :
    ∑ k ∈ Finset.range m, ∑ j : Fin τ,
        (if τ < visitCount sa k (sa k j) then 1 / Real.sqrt (visitCount sa k (sa k j)) else 0)
      ≤ Real.sqrt (8 * (S : ℝ) * A * ((m : ℝ) * τ)) := by sorry

end PosteriorSamplingRL.Regret
