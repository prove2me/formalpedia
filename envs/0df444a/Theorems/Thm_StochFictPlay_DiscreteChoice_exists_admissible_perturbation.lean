-- Prove2me | Theorems.Thm_StochFictPlay_DiscreteChoice_exists_admissible_perturbation
-- name    : StochFictPlay.DiscreteChoice.exists_admissible_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:46:58.191265+00:00
-- url     : https://prove2.me/theorems/d555a301-b998-4898-b444-2506e08c2a67
-- title:
--   Theorem 2.1 — every additive random utility choice function has an admissible deterministic perturbation representation
-- statement:
--   Let $A = \{1, \dots, n\}$ with $n \ge 1$, and let the random utility vector $\varepsilon$ have a continuous, everywhere strictly positive density $f$ on $\mathbb{R}^n$. Let $C : \mathbb{R}^n \to \Delta A$ be the choice probability function $C_i(\pi) = P(\operatorname{argmax}_j\, \pi_j + \varepsilon_j = i)$, and assume $C$ is continuously differentiable. Then there exists a single admissible deterministic perturbation $V : \operatorname{int}(\Delta A) \to \mathbb{R}$ such that for every payoff vector $\pi \in \mathbb{R}^n$,
--
--   $$
--   C(\pi) = \operatorname*{argmax}_{y \in \operatorname{int}(\Delta A)} \big( y \cdot \pi - V(y) \big),
--   $$
--
--   that is, $C(\pi) \in \operatorname{int}(\Delta A)$ and $y \cdot \pi - V(y) < C(\pi) \cdot \pi - V(C(\pi))$ for every other $y \in \operatorname{int}(\Delta A)$.
--
--   Here $V$ is admissible when it is twice continuously differentiable along the simplex, its second derivative is positive definite on the tangent space $\mathbb{R}^n_0$, and the norm of its gradient tends to infinity at the boundary of the simplex.
--
--   The theorem says that random-utility choice, for any noise distribution with a positive density, can be reproduced by a deterministic agent who pays a strictly convex, boundary-repelling cost for each mixed choice. This is what lets stochastic fictitious play with arbitrary shock distributions be analysed through deterministic perturbed payoff functions.
--
--   **Formalization Note** Alternatives are indexed by `Fin n`. The perturbation $V$ is chosen once, independently of $\pi$, and the maximizer is required to be unique. The paper's hypothesis "strictly positive density" is formalized as a continuous, everywhere positive probability density: a density that is positive everywhere but tends to zero near a hyperplane can make $C$ continuously differentiable with a vanishing off-diagonal derivative, and then no twice differentiable $V$ exists. $V$ is a function on `Fin n → ℝ` of which only the values on the open simplex matter.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 5, Theorem 2.1, eq. (2)

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb
import Definitions.Def_StochFictPlay_DiscreteChoice_Simplex
import Definitions.Def_StochFictPlay_DiscreteChoice_Admissible

namespace StochFictPlay.DiscreteChoice

/-- Theorem 2.1 (Hofbauer–Sandholm 2002, p. 5): if the random utility vector `ε` has a strictly
positive density and the choice probability function `C` is continuously differentiable, then
there is one admissible deterministic perturbation `V` such that, for every payoff vector `π`,
`C(π)` is the unique maximizer of `y ↦ y · π - V(y)` over `int(ΔA)`. -/
theorem exists_admissible_perturbation {n : ℕ} (hn : 0 < n) (f : (Fin n → ℝ) → ℝ)
    (hf : IsStrictlyPositiveDensity f) (hC : ContDiff ℝ 1 (choiceProb f)) :
    ∃ V : (Fin n → ℝ) → ℝ, IsAdmissible V ∧
      ∀ π : Fin n → ℝ, choiceProb f π ∈ openSimplex n ∧
        ∀ y ∈ openSimplex n, y ≠ choiceProb f π →
          y ⬝ᵥ π - V y < choiceProb f π ⬝ᵥ π - V (choiceProb f π) := by sorry

end StochFictPlay.DiscreteChoice
