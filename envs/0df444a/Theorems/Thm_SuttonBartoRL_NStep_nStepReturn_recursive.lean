-- Prove2me | Theorems.Thm_SuttonBartoRL_NStep_nStepReturn_recursive
-- name    : SuttonBartoRL.NStep.nStepReturn_recursive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:58:36.94488+00:00
-- url     : https://prove2.me/theorems/6c543818-4cf5-46c0-89eb-17de137cb890
-- title:
--   Recursive form of the $n$-step return (Eq. (7.12))
-- statement:
--   Consider an episode that terminates at time $T$, a discount factor $\gamma$, and the $n$-step return (7.1) ending at horizon $h$, bootstrapping from a fixed value estimate $V$ (the book's $V_{h-1}$). Then $G_{h:h} = V(S_h)$ and
--   $$G_{t:h} = R_{t+1} + \gamma\, G_{t+1:h}, \qquad t < h < T.$$
--
--   This recursion is the starting point of the per-decision off-policy returns (7.13) and (7.14).
--
--   **Formalization Note** The return is defined in closed form, $G_{t:h} = \sum_{k=0}^{h-t-1}\gamma^k R_{t+k+1} + \gamma^{h-t} V(S_h)$ for $h < T$, so the recursion and the value at $t = h$ are statements to prove, not definitions.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (7.12), p. 150

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_EpisodeReturns

namespace SuttonBartoRL.NStep

/-- Sutton & Barto (2018), (7.12), p. 150: for the `n` steps ending at horizon `h`, the `n`-step
return (7.1) (with a fixed bootstrap estimate `V`, the book's `V_{h−1}`) satisfies
`G_{h:h} = V(S_h)` and `G_{t:h} = R_{t+1} + γ G_{t+1:h}` for `t < h < T`. -/
theorem nStepReturn_recursive {S : Type} (γ : ℝ) (R : ℕ → ℝ) (St : ℕ → S) (T : ℕ)
    (V : S → ℝ) (t h : ℕ) (hth : t < h) (hhT : h < T) :
    nStepReturn γ R St T V h h = V (St h) ∧
      nStepReturn γ R St T V t h = R (t + 1) + γ * nStepReturn γ R St T V (t + 1) h := by sorry

end SuttonBartoRL.NStep
