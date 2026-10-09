-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_prop_3_1_c
-- name    : WiesemannRMDP.SRect.prop_3_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:42.341141+00:00
-- url     : https://prove2.me/theorems/6ddfc834-0957-4fd8-b76d-fc53ffc92a14
-- title:
--   Proposition 3.1 (c) — if w ≤ r̂(π; ξ) + λP̂(π; ξ)w, then w ≤ v(π; ξ)
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions. Fix $\pi\in\Pi$ and $\xi\in\Xi$. If $w\in\mathbb R^S$ satisfies
--   $$w \le \widehat r(\pi;\xi) + \lambda\,\widehat P(\pi;\xi)\,w$$
--   componentwise, then $w\le v(\pi;\xi)$ componentwise, where $v(\pi;\xi)$ is the reward to-go (8).
--
--   Every sub-solution of the policy evaluation equation lies below the reward to-go. This comparison principle is what turns the maximization of $p_0^\top w$ over sub-solutions into the evaluation of $p_0^\top v(\pi;\xi)$.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 15, Proposition 3.1 (c)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- Proposition 3.1 (c) (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610, revision of February 9, 2012, p. 15): for given `π ∈ Π` and `ξ ∈ Ξ`,
if `w ∈ ℝ^S` satisfies `w ≤ r̂(π; ξ) + λ P̂(π; ξ) w`, then `w ≤ v(π; ξ)`.

**Formalization Note.** Both inequalities are componentwise on `ℝ^S`. `v` is the series (8). -/
theorem prop_3_1_c {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) (ξ : Fin q → ℝ) (hξ : ξ ∈ M.Xi) (w : St → ℝ)
    (hw : w ≤ M.rhat π ξ + M.lam • (M.Phat π ξ *ᵥ w)) :
    w ≤ M.v π ξ := by sorry

end WiesemannRMDP.SRect
