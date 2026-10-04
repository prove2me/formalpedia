-- Prove2me | Theorems.Thm_SennottDP_Discounted_finite_horizon_cost_tendsto
-- name    : SennottDP.Discounted.finite_horizon_cost_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:57:51.92122+00:00
-- url     : https://prove2.me/theorems/5eea75ec-f961-41bd-9cf7-b6388bf24276
-- title:
--   Lemma 4.1.1 — $v_{\theta,\alpha,n}$ increases to $V_{\theta,\alpha}$
-- statement:
--   Let $\Delta$ be a Markov decision chain, $\alpha \in (0,1)$ a discount factor and $\theta$ any policy for the infinite horizon. Let $v_{\theta,\alpha,n}$ be the $n$-horizon expected discounted cost of $\theta$ with terminal cost zero. Then $n \mapsto v_{\theta,\alpha,n}(i)$ is increasing for each state $i$, and
--   $$\lim_{n \to \infty} v_{\theta,\alpha,n}(i) = V_{\theta,\alpha}(i), \qquad i \in S,$$
--   where the limit may be $+\infty$.
--
--   This links the finite horizon criterion to the infinite horizon one and is used throughout the chapter to pass from $n$-step estimates to the discounted cost.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 61, Lemma 4.1.1

import Mathlib
import Definitions.Def_SennottDP_Discounted_Criteria

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.Discounted

/-- Sennott (1999), Lemma 4.1.1, p. 61: for every policy `θ` for the infinite horizon, the
`n`-horizon cost `v_{θ,α,n}` (terminal cost zero) is increasing in `n` and converges to
`V_{θ,α}`. The discount factor satisfies the chapter's standing assumption `α ∈ (0,1)`. -/
theorem finite_horizon_cost_tendsto {S : Type} [Countable S] {Act : Type} (M : MDC S Act)
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (θ : Policy M) (i : S) :
    Monotone (fun n : ℕ => finiteHorizonCost M θ α n i) ∧
      Tendsto (fun n : ℕ => finiteHorizonCost M θ α n i) atTop
        (𝓝 (discountedCost M θ α i)) := by sorry

end SennottDP.Discounted
