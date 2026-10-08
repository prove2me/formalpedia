-- Prove2me | Theorems.Thm_SampleComplexityRL_Exploration_eps_approx_condition
-- name    : SampleComplexityRL.Exploration.eps_approx_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:45.329988+00:00
-- url     : https://prove2.me/theorems/81577871-b3d5-47ee-a29b-7911bf9a20c5
-- title:
--   Lemma 8.5.4 — an ε-approximate transition model changes every t-value by less than εT
-- statement:
--   Let $M$ and $\hat M$ be two MDPs on the same finite state set $S$ and finite nonempty action set $A$, with the same rewards $r(s,a)\in[0,1]$ and transition models $P$ and $\hat P$. Suppose $\hat P$ is an $\varepsilon$-approximation to $P$:
--   $$
--   \sum_{s'}\big|\hat P(s'\mid s,a)-P(s'\mid s,a)\big|<\varepsilon\qquad\text{for all }s,a.
--   $$
--   Then for every $T$-step policy $\pi$, every state $s$ and every time $t<T$,
--   $$
--   \big|U_{\pi,t,\hat M}(s)-U_{\pi,t,M}(s)\big|<\varepsilon T.
--   $$
--
--   The lemma says how accurate an estimated model must be for its $T$-step values to be uniformly close to the true ones; it determines the number $m$ of visits after which $R_{max}$ treats a state as known.
--
--   **Formalization Note** Values are normalized by $1/T$, so the bound $\varepsilon T$ is on values in $[0,1]$. Both $P$ and $\hat P$ are transition kernels.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 111, Lemma 8.5.4 (with Definition 8.5.3)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_SampleComplexityRL_Exploration_Model

namespace SampleComplexityRL.Exploration

open FoundationsML.ReinforcementLearning

/-- **Lemma 8.5.4 (ε-Approximation Condition)** (Kakade 2003, p. 111). Let `M = (P, r)` and
`M̂ = (P̂, r)` be two MDPs with the same rewards (in `[0,1]`) and the same state-action space. If
`P̂` is an `ε`-approximation to `P` (Definition 8.5.3), then for all deterministic `T`-step
policies `π`, states `s` and times `t < T`, `|U_{π,t,M̂}(s) − U_{π,t,M}(s)| < εT`. -/
theorem eps_approx_condition {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A]
    (P Phat : S → A → S → ℝ) (r : S → A → ℝ) (hP : IsTransitionKernel P)
    (hPhat : IsTransitionKernel Phat) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ 1)
    (ε : ℝ) (happrox : IsEpsApprox Phat P ε)
    (T : ℕ) (π : ℕ → S → A) (t : ℕ) (ht : t < T) (s : S) :
    |uValue Phat r T π t s - uValue P r T π t s| < ε * T := by sorry

end SampleComplexityRL.Exploration
