-- Prove2me | Theorems.Thm_SuttonBartoRL_BatchTD_batch_mc_converges_to_sample_average
-- name    : SuttonBartoRL.BatchTD.batch_mc_converges_to_sample_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:00:22.720983+00:00
-- url     : https://prove2.me/theorems/035640ab-47a5-4b79-94e3-8f77f2af3ca6
-- title:
--   Batch constant-$\alpha$ MC converges to the sample averages of the returns
-- statement:
--   Fix a finite batch of episodes over a finite set $\mathcal S$ of nonterminal states and $\gamma \in [0, 1]$. Consider batch-updating constant-$\alpha$ MC,
--
--   $$
--   V_{m+1}(s) = V_m(s) + \alpha \sum_{\text{visits } t \text{ of } s} \big[G_t - V_m(S_t)\big].
--   $$
--
--   There is $\bar\alpha > 0$, depending only on the batch, such that for every $\alpha \in (0, \bar\alpha)$ and every initial array $V_0$,
--
--   $$
--   \lim_{m \to \infty} V_m(s) = \bar G(s) \quad \text{for every visited } s,
--   $$
--
--   where $\bar G(s)$ is the sample average of the returns after the visits to $s$; an unvisited state keeps $V_0(s)$.
--
--   The limit does not depend on $\alpha$ or $V_0$: this is the "different answer" to which batch MC converges, to be compared with the certainty-equivalence estimate of batch TD(0).
--
--   **Formalization Note** "As long as $\alpha$ is chosen sufficiently small" is encoded as the existence of a threshold $\bar\alpha > 0$ valid for all $\alpha$ below it and all $V_0$. The book does not mention unvisited states; they receive no increment, so their value is constant.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §6.3, p. 126 (batch updating) and p. 127 (sample averages)

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

open Filter Topology

namespace SuttonBartoRL.BatchTD

/-- §6.3, pp. 126–127: under batch updating, constant-α MC converges deterministically, for every
sufficiently small `α` and every initial array, to the sample averages of the returns experienced
after visiting each state. States never visited keep their initial value. -/
theorem batch_mc_converges_to_sample_average {S : Type} [Fintype S] [DecidableEq S]
    (b : Batch S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, 0 < α → α < αbar → ∀ (V₀ : S → ℝ) (s : S),
      Tendsto (fun m : ℕ => batchMC α γ b V₀ m s) atTop
        (𝓝 (if visitCount b s = 0 then V₀ s else mcAverage γ b s)) := by sorry

end SuttonBartoRL.BatchTD
