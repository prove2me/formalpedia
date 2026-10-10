-- Prove2me | Theorems.Thm_PosteriorSamplingRL_Regret_appB_small_count_bound
-- name    : PosteriorSamplingRL.Regret.appB_small_count_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:07:39.206288+00:00
-- url     : https://prove2.me/theorems/229ec504-4f2a-422b-a299-9ca443a278c6
-- title:
--   App. B, p. 10 — Σ_k Σ_i 1(N_{t_k}(s,a) ≤ τ) ≤ 2τSA
-- statement:
--   Let $(s_{k,i},a_{k,i})$, $k=1,2,\dots$, $i=1,\dots,\tau$, be any sequence of state–action pairs in $\mathcal S\times\mathcal A$ with $|\mathcal S|=S$, $|\mathcal A|=A$, and let $N_{t_k}(s,a)$ be the number of occurrences of $(s,a)$ in the episodes before $k$. Then for every $m$,
--   $$
--   \sum_{k=1}^m\sum_{i=1}^\tau\mathbf 1\big(N_{t_k}(s_{k,i},a_{k,i})\le\tau\big)\le2\tau SA .
--   $$
--
--   Each pair can be visited in an episode that starts with at most $\tau$ earlier visits at most $2\tau$ times in total. The bound controls the part of the width sum in which the counts are still small.
--
--   **Formalization Note** The page says "fewer than 2τ times", but the count can equal $2\tau$ (one pair visited $\tau$ times in each of two episodes); the display's $\le2\tau SA$ is what is stated. The statement is deterministic: it holds for every visit sequence, in particular for the pairs visited by a PSRL run.
-- source:
--   arXiv:1306.0940v5, App. B, p. 10, first count

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Confidence

namespace PosteriorSamplingRL.Regret

/-- App. B (arXiv:1306.0940v5, p. 10), first count: for any sequence of state–action pairs
`(s_{k,j}, a_{k,j})` (episode `k`, step `j`), with `N_{t_k}(s, a)` the number of visits before
episode `k`, `∑_{k=1}^m ∑_{i=1}^τ 1(N_{t_k}(s_{k,i}, a_{k,i}) ≤ τ) ≤ 2τSA`. -/
theorem appB_small_count_bound (S A τ : ℕ) (sa : ℕ → Fin τ → Fin S × Fin A) (m : ℕ) :
    ∑ k ∈ Finset.range m, ∑ j : Fin τ,
        (if visitCount sa k (sa k j) ≤ τ then (1 : ℝ) else 0)
      ≤ 2 * (τ : ℝ) * S * A := by sorry

end PosteriorSamplingRL.Regret
