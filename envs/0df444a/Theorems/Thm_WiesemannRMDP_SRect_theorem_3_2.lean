-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_theorem_3_2
-- name    : WiesemannRMDP.SRect.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:12.227406+00:00
-- url     : https://prove2.me/theorems/73c1c36d-bfd6-44b0-90ad-f53add33a894
-- title:
--   Theorem 3.2 — over an s-rectangular set, the constant w* (fixed point of (11)) solves the policy evaluation problem (10)
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions, assume the ambiguity set $\mathcal P$ is s-rectangular, and fix a policy $\pi\in\Pi$. The robust evaluation map $\phi(\pi;\cdot)$ of (11) has a unique fixed point $w^*\in\mathbb R^S$, and the constant reward to-go function $\vartheta^*(\xi):=w^*$, $\xi\in\Xi$, optimizes the policy evaluation problem
--   $$\sup_{\vartheta:\Xi\overset{c}{\to}\mathbb R^S}\Big\{\inf_{\xi\in\Xi}\{p_0^\top\vartheta(\xi)\} : \vartheta(\xi)\le\widehat r(\pi;\xi)+\lambda\widehat P(\pi;\xi)\vartheta(\xi)\ \forall\xi\in\Xi\Big\}. \tag{10}$$
--   Precisely:
--
--   1. $\vartheta^*$ is feasible: $w^*\le\widehat r(\pi;\xi)+\lambda\widehat P(\pi;\xi)w^*$ for every $\xi\in\Xi$;
--   2. its objective value is $p_0^\top w^*$;
--   3. every continuous feasible $\vartheta$ satisfies $\inf_{\xi\in\Xi}p_0^\top\vartheta(\xi)\le p_0^\top w^*$;
--   4. $p_0^\top w^* = \inf_{\xi\in\Xi}p_0^\top v(\pi;\xi)$, the worst-case expected total reward of $\pi$.
--
--   Over s-rectangular ambiguity sets the robust policy evaluation problem therefore reduces to a fixed-point computation in $\mathbb R^S$. Without s-rectangularity the conclusion fails (Example 3.11 of the paper).
--
--   **Formalization Note.** The comparison class is every reward to-go function continuous on $\Xi$, not only the constant ones. Item 4 is the second step of the paper's proof ((10) = (15), p. 17).
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), p. 16, Theorem 3.2 (with (11))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- Theorem 3.2 (Wiesemann, Kuhn & Rustem, *Robust Markov Decision Processes*, Optimization
Online 2610, revision of February 9, 2012, p. 16): for an s-rectangular ambiguity set `𝒫`, the
policy evaluation problem (10) is optimized by the constant reward to-go function
`ϑ∗(ξ) := w∗`, `ξ ∈ Ξ`, where `w∗ ∈ ℝ^S` is the unique fixed point of the contraction mapping
`φ(π; ·)` of (11).

The conclusions: `φ(π; ·)` has a unique fixed point; and for that fixed point `w∗`,
1. the constant function `ξ ↦ w∗` is feasible in (10);
2. its objective value is `p₀ᵀ w∗`;
3. every reward to-go function `ϑ` continuous on `Ξ` and feasible in (10) has
   `inf_{ξ∈Ξ} p₀ᵀ ϑ(ξ) ≤ p₀ᵀ w∗`;
4. `p₀ᵀ w∗ = inf_{ξ∈Ξ} p₀ᵀ v(π; ξ)`, the worst-case expected total reward (6) (the second
   step of the proof, (10) = (15), p. 17).

**Formalization Note.** The comparison class is every continuous `ϑ : Ξ → ℝ^S` (`Ξ ↦c ℝ^S` in
(10)), not the constant functions only. s-rectangularity (`Model.IsSRectangular`) is a
hypothesis; without it the statement fails (Example 3.11, p. 24). -/
theorem theorem_3_2 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (hrect : M.IsSRectangular) (π : St → Act → ℝ) (hπ : IsPolicy π) :
    (∃! w : St → ℝ, M.phiEval π w = w) ∧
    ∀ wstar : St → ℝ, M.phiEval π wstar = wstar →
      M.Feasible π (fun _ => wstar) ∧
      M.objective (fun _ => wstar) = M.p0 ⬝ᵥ wstar ∧
      (∀ ϑ : (Fin q → ℝ) → St → ℝ, ContinuousOn ϑ M.Xi → M.Feasible π ϑ →
        M.objective ϑ ≤ M.p0 ⬝ᵥ wstar) ∧
      M.p0 ⬝ᵥ wstar = M.objective (fun ξ => M.v π ξ) := by sorry

end WiesemannRMDP.SRect
