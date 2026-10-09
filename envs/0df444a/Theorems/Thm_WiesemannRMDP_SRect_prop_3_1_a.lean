-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_prop_3_1_a
-- name    : WiesemannRMDP.SRect.prop_3_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:40:02.54803+00:00
-- url     : https://prove2.me/theorems/a52874d4-1969-4108-94a6-f18ebf6d18ca
-- title:
--   Proposition 3.1 (a) — the reward to-go v is Lipschitz continuous on Π × Ξ
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions. The reward to-go
--   $$(\pi,\xi)\ \mapsto\ v(\pi;\xi) = \sum_{t=0}^\infty\big[\lambda\widehat P(\pi;\xi)\big]^t\,\widehat r(\pi;\xi)\in\mathbb R^S$$
--   is Lipschitz continuous on $\Pi\times\Xi$: there is a constant $C\ge 0$ with $\|v(\pi;\xi)-v(\pi';\xi')\|\le C\,\|(\pi,\xi)-(\pi',\xi')\|$ for all $\pi,\pi'\in\Pi$ and $\xi,\xi'\in\Xi$.
--
--   In particular $\xi\mapsto v(\pi;\xi)$ is continuous on $\Xi$, so it belongs to the class of continuous reward to-go functions over which problems (10) and (24) optimize.
--
--   **Formalization Note.** $\Pi$ is a subset of $\mathbb R^{S\times A}$ (policies as functions $\pi(a\mid s)$) and $\Xi\subseteq\mathbb R^q$; the domain and $\mathbb R^S$ carry Mathlib's sup metrics. All norms on these finite-dimensional spaces are equivalent, so the existence of a Lipschitz constant does not depend on this choice.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 15, Proposition 3.1 (a)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- Proposition 3.1 (a) (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*,
Optimization Online 2610, revision of February 9, 2012, p. 15): `v` is Lipschitz continuous on
`Π × Ξ`.

**Formalization Note.** `Π × Ξ` is the subset `{π | IsPolicy π} ×ˢ Ξ` of
`(S → A → ℝ) × ℝ^q`, with the sup (product) metrics of Mathlib on the domain and on `ℝ^S`. All
norms on these finite-dimensional spaces are equivalent, so the existence of a Lipschitz constant
does not depend on this choice. -/
theorem prop_3_1_a {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing) :
    ∃ C : NNReal, LipschitzOnWith C (fun x : (St → Act → ℝ) × (Fin q → ℝ) => M.v x.1 x.2)
      ({π : St → Act → ℝ | IsPolicy π} ×ˢ M.Xi) := by sorry

end WiesemannRMDP.SRect
