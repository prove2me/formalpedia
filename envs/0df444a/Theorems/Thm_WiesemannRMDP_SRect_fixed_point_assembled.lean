-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_fixed_point_assembled
-- name    : WiesemannRMDP.SRect.fixed_point_assembled
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:53.148528+00:00
-- url     : https://prove2.me/theorems/8c29c431-4241-4aff-a208-e18025494438
-- title:
--   §4, proof of Theorem 4.1, p. 26 — the policy π* assembled from per-state maximizers satisfies w* = φ(π*; w*)
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions. Let $w^*\in\mathbb R^S$ be a fixed point of the robust improvement map
--   $$\varphi_s(w) := \max_{\pi\in\Pi}\phi_s(\pi;w),\qquad s\in\mathcal S, \tag{25}$$
--   where $\phi$ is the robust evaluation map (11). For every state $s$ let $\pi^s\in\Pi$ attain $\max_{\pi\in\Pi}\phi_s(\pi;w^*)$, and define $\pi^*(a\mid s):=\pi^s(a\mid s)$. Then $\pi^*\in\Pi$ and
--   $$w^* = \phi(\pi^*;w^*).$$
--
--   The point is that $\phi_s(\pi;w)$ depends on $\pi$ only through the row $\pi(\cdot\mid s)$, so per-state maximizers can be glued into one stationary policy. In particular $(\pi^*,w^*)$ is feasible in the reformulated improvement problem (26), $\max\{p_0^\top w : \exists\pi\in\Pi,\ w\le\phi(\pi;w)\}$.
--
--   **Formalization Note.** In Lean, (11) is `phiEval` and (25) is `phiImprove`. No rectangularity is assumed.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), §4, proof of Theorem 4.1, p. 26

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- §4, proof of Theorem 4.1, p. 26 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision
Processes*, Optimization Online 2610, revision of February 9, 2012): "Note that φ_s only depends
on the components π(·|s) of π. Hence, we have w∗ = φ(π∗; w∗)".

Let `w∗` be a fixed point of the improvement map `ϕ` of (25). For each state `s` let `π^s ∈ Π`
attain `max_{π∈Π} φ_s(π; w∗)`, and let `π∗(a|s) := π^s(a|s)`. Then `π∗ ∈ Π` and
`w∗ = φ(π∗; w∗)`.

**Formalization Note.** `πs s` is the policy `π^s`; `πs s s a` is `π^s(a|s)`. The maximizing
property is stated against every `π ∈ Π`. No rectangularity is assumed. -/
theorem fixed_point_assembled {St Act : Type*} [Fintype St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (wstar : St → ℝ) (hfix : M.phiImprove wstar = wstar)
    (πs : St → St → Act → ℝ) (hπs : ∀ s, IsPolicy (πs s))
    (hmax : ∀ s, ∀ π : St → Act → ℝ, IsPolicy π → M.phiEval π wstar s ≤ M.phiEval (πs s) wstar s) :
    IsPolicy (fun s a => πs s s a) ∧ M.phiEval (fun s a => πs s s a) wstar = wstar := by sorry

end WiesemannRMDP.SRect
