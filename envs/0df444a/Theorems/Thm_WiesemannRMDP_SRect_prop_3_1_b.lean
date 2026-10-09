-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_prop_3_1_b
-- name    : WiesemannRMDP.SRect.prop_3_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:51.813676+00:00
-- url     : https://prove2.me/theorems/af229f03-4363-41a2-b496-6fd47497dafc
-- title:
--   Proposition 3.1 (b) — w = r̂(π; ξ) + λP̂(π; ξ)w if and only if w = v(π; ξ)
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions. Fix a stationary randomized policy $\pi\in\Pi$ and a parameter $\xi\in\Xi$, and let $\widehat P(\pi;\xi)$, $\widehat r(\pi;\xi)$ be the transition matrix and expected state rewards (7a)–(7b) of the induced Markov reward process. Then a vector $w\in\mathbb R^S$ satisfies the policy evaluation equation
--   $$w = \widehat r(\pi;\xi) + \lambda\,\widehat P(\pi;\xi)\,w$$
--   if and only if $w = v(\pi;\xi)$, where $v(\pi;\xi)=\sum_{t\ge 0}[\lambda\widehat P(\pi;\xi)]^t\widehat r(\pi;\xi)$ is the reward to-go (8).
--
--   The evaluation equation therefore characterizes the reward to-go; this is used to identify the optimal value of the robust evaluation problem with the worst-case expected reward.
--
--   **Formalization Note.** The reward to-go is defined by the series (8), not by the equation, so the statement is not definitional.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 15, Proposition 3.1 (b)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- Proposition 3.1 (b) (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610, revision of February 9, 2012, p. 15): for given `π ∈ Π` and `ξ ∈ Ξ`,
`w ∈ ℝ^S` satisfies `w = r̂(π; ξ) + λ P̂(π; ξ) w` if and only if `w = v(π; ξ)`.

**Formalization Note.** `v` is the series (8) (`Model.v`), not the solution of the equation, so
the statement has content. The standing assumptions of §1–§2.1 are `Model.Standing`;
`Π` is the set of stationary randomized policies (`IsPolicy`). -/
theorem prop_3_1_b {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) (ξ : Fin q → ℝ) (hξ : ξ ∈ M.Xi) (w : St → ℝ) :
    w = M.rhat π ξ + M.lam • (M.Phat π ξ *ᵥ w) ↔ w = M.v π ξ := by sorry

end WiesemannRMDP.SRect
