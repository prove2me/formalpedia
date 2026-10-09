-- Prove2me | Theorems.Thm_WiesemannRMDP_SRect_eq_10
-- name    : WiesemannRMDP.SRect.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:53.50157+00:00
-- url     : https://prove2.me/theorems/630a95d2-af0d-4d18-a568-9a9acca2a3b8
-- title:
--   (10), p. 15 — inf_ξ p₀ᵀv(π; ξ) equals the robust evaluation problem over all, and over continuous, reward to-go functions
-- statement:
--   Consider the robust MDP of the module `WiesemannRMDP.SRect.Model` under its standing assumptions, and fix a policy $\pi\in\Pi$. The worst-case expected total reward of $\pi$ admits the reformulation
--   $$\begin{aligned}\inf_{\xi\in\Xi}\{p_0^\top v(\pi;\xi)\} &= \inf_{\xi\in\Xi}\ \sup_{w\in\mathbb R^S}\big\{p_0^\top w : w\le\widehat r(\pi;\xi)+\lambda\widehat P(\pi;\xi)w\big\}\\ &= \sup_{\vartheta:\Xi\to\mathbb R^S}\Big\{\inf_{\xi\in\Xi}\{p_0^\top\vartheta(\xi)\} : \vartheta(\xi)\le\widehat r(\pi;\xi)+\lambda\widehat P(\pi;\xi)\vartheta(\xi)\ \forall\xi\in\Xi\Big\}\\ &= \sup_{\vartheta:\Xi\overset{c}{\to}\mathbb R^S}\Big\{\inf_{\xi\in\Xi}\{p_0^\top\vartheta(\xi)\} : \vartheta(\xi)\le\widehat r(\pi;\xi)+\lambda\widehat P(\pi;\xi)\vartheta(\xi)\ \forall\xi\in\Xi\Big\},\end{aligned}\tag{10}$$
--   where the last supremum is over functions continuous on $\Xi$. Precisely:
--
--   1. for every $\xi\in\Xi$, $p_0^\top v(\pi;\xi)$ is the largest value of $p_0^\top w$ over all $w$ with $w\le\widehat r(\pi;\xi)+\lambda\widehat P(\pi;\xi)w$ (the inner supremum is attained);
--   2. over all functions $\vartheta:\Xi\to\mathbb R^S$ feasible for $\pi$, the largest value of $\inf_{\xi\in\Xi}p_0^\top\vartheta(\xi)$ (in the extended reals) is $\inf_{\xi\in\Xi}p_0^\top v(\pi;\xi)$;
--   3. over all continuous $\vartheta$ feasible for $\pi$, the largest value of $\inf_{\xi\in\Xi}p_0^\top\vartheta(\xi)$ is $\inf_{\xi\in\Xi}p_0^\top v(\pi;\xi)$.
--
--   The last line is the robust policy evaluation problem (10) that Theorem 3.2 solves over s-rectangular ambiguity sets.
--
--   **Formalization Note.** The suprema are stated as attained maxima (greatest elements). For a non-continuous $\vartheta$ the infimum over $\Xi$ can be $-\infty$, so line 2 is computed in the extended reals.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), §3, p. 15, (10)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_WiesemannRMDP_SRect_Model

namespace WiesemannRMDP.SRect

open FoundationsML.ReinforcementLearning Matrix

/-- The reformulation (10) of the worst-case expected total reward (Wiesemann, Kuhn & Rustem,
*Robust Markov Decision Processes*, Optimization Online 2610, revision of February 9, 2012,
§3, (10), p. 15): for a fixed policy `π ∈ Π`,
```
inf_{ξ∈Ξ} {p₀ᵀ v(π; ξ)} = inf_{ξ∈Ξ} sup_{w∈ℝ^S} {p₀ᵀw : w ≤ r̂(π; ξ) + λ P̂(π; ξ) w}
  = sup_{ϑ:Ξ↦ℝ^S} { inf_{ξ∈Ξ} {p₀ᵀϑ(ξ)} : ϑ(ξ) ≤ r̂(π; ξ) + λ P̂(π; ξ) ϑ(ξ) ∀ ξ ∈ Ξ }
  = sup_{ϑ:Ξ↦cℝ^S} { inf_{ξ∈Ξ} {p₀ᵀϑ(ξ)} : ϑ(ξ) ≤ r̂(π; ξ) + λ P̂(π; ξ) ϑ(ξ) ∀ ξ ∈ Ξ }.
```

The three conclusions are, in order:
1. for every `ξ ∈ Ξ`, `p₀ᵀ v(π; ξ)` is the greatest element (an attained supremum) of
   `{p₀ᵀ w : w ≤ r̂(π; ξ) + λ P̂(π; ξ) w}`; this gives the first equality;
2. the middle line: over all functions `ϑ` feasible for `π`, the greatest value of
   `inf_{ξ∈Ξ} p₀ᵀ ϑ(ξ)` is `inf_{ξ∈Ξ} p₀ᵀ v(π; ξ)`, computed in `EReal`;
3. the last line: over all `ϑ` continuous on `Ξ` and feasible for `π`, the greatest value of
   `inf_{ξ∈Ξ} p₀ᵀ ϑ(ξ)` is `inf_{ξ∈Ξ} p₀ᵀ v(π; ξ)`.

**Formalization Note.** Suprema are stated as greatest elements (`IsGreatest`), so no junk value
of a real `sSup` enters. For an arbitrary (not continuous) `ϑ` the infimum over `Ξ` may be
`-∞`; the middle line is therefore computed in `EReal`, where that infimum is `⊥` rather than
the real `iInf` junk value `0`. `Model.objective ϑ` is the real infimum
`inf_{ξ∈Ξ} p₀ᵀ ϑ(ξ)`, finite for continuous `ϑ` on the compact set `Ξ`. -/
theorem eq_10 {St Act : Type*} [Fintype St] [DecidableEq St] [Fintype Act]
    [Nonempty St] [Nonempty Act] {q L : ℕ} (M : Model St Act q L) (hM : M.Standing)
    (π : St → Act → ℝ) (hπ : IsPolicy π) :
    (∀ ξ ∈ M.Xi, IsGreatest
        {x : ℝ | ∃ w : St → ℝ, w ≤ M.rhat π ξ + M.lam • (M.Phat π ξ *ᵥ w) ∧ x = M.p0 ⬝ᵥ w}
        (M.p0 ⬝ᵥ M.v π ξ)) ∧
    IsGreatest
        {x : EReal | ∃ ϑ : (Fin q → ℝ) → St → ℝ, M.Feasible π ϑ ∧
            x = ⨅ ξ : M.Xi, ((M.p0 ⬝ᵥ ϑ ξ : ℝ) : EReal)}
        ((M.objective (fun ξ => M.v π ξ) : ℝ) : EReal) ∧
    IsGreatest
        {x : ℝ | ∃ ϑ : (Fin q → ℝ) → St → ℝ, ContinuousOn ϑ M.Xi ∧ M.Feasible π ϑ ∧
            x = M.objective ϑ}
        (M.objective (fun ξ => M.v π ξ)) := by sorry

end WiesemannRMDP.SRect
