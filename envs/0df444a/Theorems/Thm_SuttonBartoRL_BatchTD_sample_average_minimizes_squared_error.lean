-- Prove2me | Theorems.Thm_SuttonBartoRL_BatchTD_sample_average_minimizes_squared_error
-- name    : SuttonBartoRL.BatchTD.sample_average_minimizes_squared_error
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:59:56.794116+00:00
-- url     : https://prove2.me/theorems/a2a98871-c7a3-43ff-a89a-997f685bfd4c
-- title:
--   Sample averages of the returns minimize the squared error on the training set
-- statement:
--   Fix a finite batch of episodes over a finite set $\mathcal S$ of nonterminal states and $\gamma \in [0, 1]$. Let $\bar G(s)$ be the sample average of the returns observed after the visits to $s$ (every visit counted). For every value array $V : \mathcal S \to \mathbb R$,
--
--   $$
--   \sum_{\text{episodes}} \sum_{t < T} \big(G_t - \bar G(S_t)\big)^2 \;\le\; \sum_{\text{episodes}} \sum_{t < T} \big(G_t - V(S_t)\big)^2 .
--   $$
--
--   The sample averages, which batch constant-$\alpha$ MC converges to, are thus the least-squares fit of a value array to the observed returns, the sense in which the batch Monte Carlo answer is optimal.
--
--   **Formalization Note** The book speaks of the *mean* square error; dividing both sides by the total number of visits does not change the minimizer, so the total squared error is used.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §6.3, p. 127; restated p. 128

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

namespace SuttonBartoRL.BatchTD

/-- §6.3, p. 127: the sample averages of the returns are optimal estimates in the sense that they
minimize the squared error from the actual returns in the training set: no array `V` has a
smaller total squared error `Σ_{visits} (G_t − V(S_t))²`. -/
theorem sample_average_minimizes_squared_error {S : Type} [Fintype S] [DecidableEq S]
    (b : Batch S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (V : S → ℝ) :
    mcSquaredError γ b (mcAverage γ b) ≤ mcSquaredError γ b V := by sorry

end SuttonBartoRL.BatchTD
