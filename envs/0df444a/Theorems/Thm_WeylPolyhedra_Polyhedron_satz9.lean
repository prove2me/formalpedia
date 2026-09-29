-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_satz9
-- name    : WeylPolyhedra.Polyhedron.satz9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:06:18.33718+00:00
-- url     : https://prove2.me/theorems/17be033e-b8e2-4602-a8c3-79fb898ef654
-- title:
--   Satz 9: if $S$ is non-degenerate and $(S)$ has an inner point, $\Sigma$ is non-degenerate
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite non-degenerate system of homogeneous inequalities $(a\xi) \ge 0$, $a \in S$, and suppose $(S)$ has an **inner point** $\xi^0$, i.e. $(a\xi^0) > 0$ for every $a \in S$. Then the dual system $\Sigma$ is non-degenerate as well: if $p \in \mathbb{R}^n$ satisfies
--   $$(\alpha p) = 0 \quad \text{for every extreme solution } \alpha \text{ of } S,$$
--   then $p = 0$.
--
--   Satz 9 is what makes the duality between $S$ and $\Sigma$ symmetric; in §4 II it shows that the system of extreme solutions attached to a bounded region is non-degenerate.
--
--   (Weyl: "Satz 9. Ist S nicht-ausgeartet und enthält (S) einen inneren Punkt, so ist auch Σ nicht-ausgeartet.")
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 299, §3 III, Satz 9

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §3 III, p. 299, Satz 9: let `S ⊆ ℝⁿ` be a finite non-degenerate system of
inequalities `a ⬝ᵥ ξ ≥ 0` whose region `(S)` contains an inner point `ξ⁰`
(`a ⬝ᵥ ξ⁰ > 0` for every `a ∈ S`). Then the dual system `Σ` is non-degenerate: the only `p`
with `α ⬝ᵥ p = 0` for every extreme solution `α` of `S` is `p = 0`. -/
theorem satz9 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    ∀ p : Fin n → ℝ, (∀ α : Fin n → ℝ, IsExtremeSolution S α → α ⬝ᵥ p = 0) → p = 0 := by sorry

end WeylPolyhedra.Polyhedron
