-- Prove2me | Theorems.Thm_WiesemannRMDP_AffineSDP_prop_3_1_c
-- name    : WiesemannRMDP.AffineSDP.prop_3_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:40:52.887016+00:00
-- url     : https://prove2.me/theorems/0eb382fa-e19d-40e2-80c5-d85494d6cf5d
-- title:
--   Proposition 3.1 (c) — sub-solutions w ≤ r̂(π; ξ) + λP̂(π; ξ)w lie below the reward to-go v(π; ξ)
-- statement:
--   Consider the robust MDP with affine ambiguity set under its standing assumptions, a stationary randomized policy $\pi\in\Pi$ and a parameter $\xi\in\Xi$. If a vector $w\in\mathbb R^S$ satisfies
--   $$w \le \widehat r(\pi;\xi) + \lambda\,\widehat P(\pi;\xi)\,w$$
--   componentwise, then
--   $$w \le v(\pi;\xi),$$
--   where $v(\pi;\xi)=\sum_{t\ge 0}[\lambda\widehat P(\pi;\xi)]^t\widehat r(\pi;\xi)$ is the reward to-go.
--
--   The reward to-go is thus the largest sub-solution of the policy evaluation equation; this is what turns the policy evaluation problem into the optimization problems (10) and (19) over sub-solutions.
--
--   **Formalization Note.** Both inequalities are componentwise. The reward to-go is defined by the series (8).
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 15, Proposition 3.1 (c)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_AffineSDP_ParamSet
import Definitions.Def_WiesemannRMDP_AffineSDP_Model
import Definitions.Def_WiesemannRMDP_AffineSDP_Programs

namespace WiesemannRMDP.AffineSDP

open FoundationsML.ReinforcementLearning Matrix

/-- Proposition 3.1 (c) (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610, revision of February 9, 2012, p. 15): for given `π ∈ Π` and `ξ ∈ Ξ`,
if `w ∈ ℝ^S` satisfies `w ≤ r̂(π; ξ) + λ P̂(π; ξ) w`, then `w ≤ v(π; ξ)`.

**Formalization Note.** Both inequalities are componentwise on `ℝ^S`. `v` is the series (8).
`Π` is the set of stationary randomized policies (`IsPolicy`). -/
theorem prop_3_1_c {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) (ξ : Fin q → ℝ) (hξ : ξ ∈ M.Xi) (w : St → ℝ)
    (hw : w ≤ M.rhat π ξ + M.lam • (M.Phat π ξ *ᵥ w)) :
    w ≤ M.v π ξ := by sorry

end WiesemannRMDP.AffineSDP
