-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_theorem_4_1
-- name    : WiesemannRMDP.SRect.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:27.147112+00:00
-- url     : https://prove2.me/theorems/85ed668e-cc16-46dc-b5cb-da102f6fce07
-- title:
--   Theorem 4.1 — over an s-rectangular ambiguity set, π* and the constant ϑ* = w* solve the robust policy improvement problem (24)
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions, and assume the ambiguity set $\mathcal P$ is s-rectangular. The robust policy improvement problem is
--   $$\sup_{\pi\in\Pi}\ \sup_{\vartheta:\Xi\overset{c}{\to}\mathbb R^S}\Big\{\inf_{\xi\in\Xi}\{p_0^\top\vartheta(\xi)\} : \vartheta(\xi)\le\widehat r(\pi;\xi)+\lambda\widehat P(\pi;\xi)\vartheta(\xi)\ \forall\xi\in\Xi\Big\}, \tag{24}$$
--   the inner supremum ranging over reward to-go functions continuous on $\Xi$. Let
--   $$\varphi_s(w) := \max_{\pi\in\Pi}\phi_s(\pi;w),\qquad s\in\mathcal S, \tag{25}$$
--   with $\phi$ the robust evaluation map (11). Then:
--
--   1. $\varphi$ has a unique fixed point $w^*\in\mathbb R^S$;
--   2. for every state $s$ there is a policy $\pi^s\in\arg\max_{\pi\in\Pi}\phi_s(\pi;w^*)$;
--   3. for every such choice of maximizers, the policy $\pi^*(a\mid s):=\pi^s(a\mid s)$ belongs to $\Pi$, the pair $(\pi^*,\vartheta^*)$ with the constant function $\vartheta^*(\xi):=w^*$ is feasible in (24) with objective value $p_0^\top w^*$, and every pair $(\pi,\vartheta)$ with $\pi\in\Pi$ and $\vartheta$ continuous on $\Xi$ and feasible for $\pi$ satisfies $\inf_{\xi\in\Xi}p_0^\top\vartheta(\xi)\le p_0^\top w^*$.
--
--   So over s-rectangular ambiguity sets an optimal robust policy can be taken stationary (possibly randomized) and is obtained, together with the optimal value $p_0^\top w^*$, from the fixed point of a robust Bellman map; this is the main structural result of the paper's robust policy improvement section.
--
--   **Formalization Note.** In Lean, (11) is `phiEval` and (25) is `phiImprove`. "Optimized by" is stated against every policy in $\Pi$ and every continuous feasible reward to-go function, as in (24). The maxima and minima of (11) and (25) are suprema and infima over subtypes, attained under the standing assumptions.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 26, Theorem 4.1 (with (24), p. 25, and (25))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- Theorem 4.1 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*, Optimization
Online 2610, revision of February 9, 2012, p. 26): for an s-rectangular ambiguity set `𝒫`, the
policy improvement problem (24),
```
sup_{π∈Π} sup_{ϑ:Ξ↦cℝ^S} { inf_{ξ∈Ξ} {p₀ᵀϑ(ξ)} : ϑ(ξ) ≤ r̂(π; ξ) + λ P̂(π; ξ) ϑ(ξ) ∀ ξ ∈ Ξ },
```
is optimized by the policy `π∗ ∈ Π` and the constant reward to-go function `ϑ∗(ξ) := w∗`,
where `w∗ ∈ ℝ^S` is the unique fixed point of the map `ϕ` of (25),
`ϕ_s(w) := max_{π∈Π} {φ_s(π; w)}`, `π^s ∈ Π` attains `max_{π∈Π} φ_s(π; w∗)` for each `s`, and
`π∗(a|s) := π^s(a|s)`.

The conclusions: `ϕ` has a unique fixed point; and for that fixed point `w∗`,
1. for every state `s` a maximizer `π^s ∈ arg max_{π∈Π} φ_s(π; w∗)` exists;
2. for every choice of such maximizers `(π^s)_{s∈S}`, the assembled policy `π∗` lies in `Π`,
   the pair `(π∗, ξ ↦ w∗)` is feasible in (24), its objective value is `p₀ᵀ w∗`, and every pair
   `(π, ϑ)` with `π ∈ Π` and `ϑ` continuous on `Ξ` and feasible for `π` has
   `inf_{ξ∈Ξ} p₀ᵀ ϑ(ξ) ≤ p₀ᵀ w∗`.

**Formalization Note.** `πs s` is the policy `π^s` and `πs s s a` is `π^s(a|s)`. The
comparison class of "optimized by" is every `π ∈ Π` together with every continuous feasible
`ϑ`, as in (24). s-rectangularity (`Model.IsSRectangular`) is a hypothesis. The maximum and
minimum in (11) and (25) are infimum and supremum over subtypes, attained under
`Model.Standing`. -/
theorem theorem_4_1 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (hrect : M.IsSRectangular) :
    (∃! w : St → ℝ, M.phiImprove w = w) ∧
    ∀ wstar : St → ℝ, M.phiImprove wstar = wstar →
      (∀ s : St, ∃ π : St → Act → ℝ, IsPolicy π ∧
        ∀ π' : St → Act → ℝ, IsPolicy π' → M.phiEval π' wstar s ≤ M.phiEval π wstar s) ∧
      ∀ πs : St → St → Act → ℝ, (∀ s, IsPolicy (πs s)) →
        (∀ s, ∀ π' : St → Act → ℝ, IsPolicy π' →
          M.phiEval π' wstar s ≤ M.phiEval (πs s) wstar s) →
        IsPolicy (fun s a => πs s s a) ∧
        M.Feasible (fun s a => πs s s a) (fun _ => wstar) ∧
        M.objective (fun _ => wstar) = M.p0 ⬝ᵥ wstar ∧
        ∀ π : St → Act → ℝ, IsPolicy π → ∀ ϑ : (Fin q → ℝ) → St → ℝ,
          ContinuousOn ϑ M.Xi → M.Feasible π ϑ → M.objective ϑ ≤ M.p0 ⬝ᵥ wstar := by sorry

end WiesemannRMDP.SRect
