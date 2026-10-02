-- Prove2me | Theorems.Thm_ScenarioApproach_Generalization_card_support_constraints_le_dim
-- name    : ScenarioApproach.Generalization.card_support_constraints_le_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T17:27:11.164116+00:00
-- url     : https://prove2.me/theorems/f70e8aa3-c51d-4c41-95da-a00af7115dd9
-- title:
--   Theorem 5.2 — a convex scenario program has at most $d$ support constraints
-- statement:
--   Let $\Theta\subseteq\mathbb R^d$ and every constraint set $\Theta_\delta\subseteq\mathbb R^d$, $\delta\in\Delta$, be convex, and let $c\in\mathbb R^d$. Fix any $m\ge 0$ and any sample $(\delta_1,\dots,\delta_m)$, and let $\theta^*$ be a solution of the scenario program
--
--   $$
--   \min_{\theta\in\Theta}c^T\theta\quad\text{subject to}\quad\theta\in\bigcap_{i=1}^m\Theta_{\delta_i}.
--   $$
--
--   Then the number of support constraints of this program (constraints whose removal allows a feasible point of strictly smaller cost than $c^T\theta^*$) is at most $d$:
--
--   $$
--   \#\{i\in\{1,\dots,m\}:\ \theta\in\Theta_{\delta_i}\ \text{is a support constraint}\}\le d .
--   $$
--
--   The statement is deterministic: it holds for every sample, with no probability involved. It is the combinatorial fact on which the generalization theory of convex scenario programs rests, since the number of scenarios that determine the solution is bounded by the number of decision variables rather than by the number of scenarios.
--
--   **Formalization Note** The book states the result for $d=2$ in Theorem 5.2 and for general $d$ in its footnote 15; the general form is stated here. Only convexity of $\Theta$ and of the $\Theta_\delta$ is assumed (closedness and uniqueness of the solution, which are in force in the chapter, are not needed for this statement). The sample is `ω : Fin m → Δ`.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 57, Theorem 5.2 and footnote 15

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram
import Definitions.Def_ScenarioApproach_Generalization_supportConstraint

namespace ScenarioApproach.Generalization

/-- Theorem 5.2 with footnote 15 (p. 57): if `Θ` and every `Θ_δ` are convex, then for every
`m` and every sample `ω : Fin m → Δ`, the scenario program with these `m` constraints has at most
`d` support constraints at any of its solutions. -/
theorem card_support_constraints_le_dim {d m : ℕ} {Δ : Type*}
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ))
    (ω : Fin m → Δ) (θstar : EuclideanSpace ℝ (Fin d)) (hθstar : IsSolution c Θ Θδ ω θstar) :
    numSupportConstraints c Θ Θδ ω θstar ≤ d := by sorry

end ScenarioApproach.Generalization
