-- Prove2me | Theorems.Thm_SuttonBartoRL_BatchTD_you_are_the_predictor
-- name    : SuttonBartoRL.BatchTD.you_are_the_predictor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:00:27.289211+00:00
-- url     : https://prove2.me/theorems/1393343a-baca-4cb5-aab5-3412ac30f4f8
-- title:
--   Example 6.4 (You are the Predictor): batch TD(0) gives $V(A) = 3/4$, batch MC gives $V(A) = 0$
-- statement:
--   Consider two nonterminal states $A$, $B$, no discounting ($\gamma = 1$), and the batch of eight episodes
--
--   $$
--   A,0,B,0 \qquad B,1 \quad (\text{six times}) \qquad B,0 .
--   $$
--
--   Then:
--
--   1. the certainty-equivalence estimate is $\hat v(A) = \hat v(B) = \tfrac34$;
--   2. the sample averages of the returns are $\bar G(A) = 0$ and $\bar G(B) = \tfrac34$;
--   3. there is $\bar\alpha > 0$ such that for every $\alpha \in (0, \bar\alpha)$ and every initial array $V_0$, batch TD(0) converges to $V(A) = V(B) = \tfrac34$, and batch constant-$\alpha$ MC converges to $V(A) = 0$, $V(B) = \tfrac34$.
--
--   The example shows the two batch answers differing on data from a single batch: the Monte Carlo answer fits the training returns exactly, while the TD answer is the one implied by the Markov model built from the data.
--
--   **Formalization Note** $A$ and $B$ are the elements $0$ and $1$ of `Fin 2`. The first episode is the list $(A, 0), (B, 0)$: from $A$ with reward $0$ to $B$, then from $B$ with reward $0$ to the terminal state.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Example 6.4, pp. 127–128

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

open Filter Topology

namespace SuttonBartoRL.BatchTD

/-- Example 6.4 "You are the Predictor", pp. 127–128. States `A = 0`, `B = 1` of `Fin 2`, `γ = 1`,
and the eight episodes `A,0,B,0`; `B,1` (six times); `B,0`. The certainty-equivalence estimate
is `V(A) = V(B) = 3/4`, which is what batch TD(0) converges to; the sample averages of the returns
are `V(A) = 0`, `V(B) = 3/4`, which is what batch Monte Carlo converges to. -/
theorem you_are_the_predictor :
    let b : Batch (Fin 2) :=
      [[((0 : Fin 2), (0 : ℝ)), (1, 0)], [(1, 1)], [(1, 1)], [(1, 1)], [(1, 1)], [(1, 1)],
        [(1, 1)], [(1, 0)]]
    ceEstimate 1 b 0 = 3 / 4 ∧ ceEstimate 1 b 1 = 3 / 4 ∧
    mcAverage 1 b 0 = 0 ∧ mcAverage 1 b 1 = 3 / 4 ∧
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, 0 < α → α < αbar → ∀ V₀ : Fin 2 → ℝ,
      Tendsto (fun m : ℕ => batchTD α 1 b V₀ m 0) atTop (𝓝 (3 / 4)) ∧
      Tendsto (fun m : ℕ => batchTD α 1 b V₀ m 1) atTop (𝓝 (3 / 4)) ∧
      Tendsto (fun m : ℕ => batchMC α 1 b V₀ m 0) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => batchMC α 1 b V₀ m 1) atTop (𝓝 (3 / 4)) := by sorry

end SuttonBartoRL.BatchTD
