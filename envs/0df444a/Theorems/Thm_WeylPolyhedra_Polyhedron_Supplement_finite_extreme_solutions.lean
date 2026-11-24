-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_finite_extreme_solutions
-- name    : WeylPolyhedra.Polyhedron.Supplement.finite_extreme_solutions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:34:52.427622+00:00
-- url     : https://prove2.me/theorems/b167f334-e3d4-4b1f-964f-61c70182188b
-- title:
--   §3 I, p. 297 — up to positive scaling there are finitely many extreme solutions
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite system of homogeneous inequalities $(a\xi) \ge 0$, $a \in S$. If positive multiples $\rho\xi$ ($\rho > 0$) are regarded as the same solution as $\xi$, then $S$ has only finitely many extreme solutions: there is a finite set $F$ of extreme solutions of $S$ such that
--   $$\text{every extreme solution } \xi \text{ of } S \text{ is } \xi = \rho f \text{ for some } f \in F,\ \rho > 0.$$
--
--   This makes the dual system $\Sigma$ effectively a finite system, so the results on finite systems (Satz 6, Satz 8) apply to it in the proof of Satz 10.
--
--   (Weyl: "I. Es gibt nur eine endliche Anzahl extremer Lösungen ξ der Ungleichungen S — wenn wir, was natürlich ist, (ρξ_1, ⋯, ρξ_n) (ρ > 0) als die gleiche Lösung wie (ξ_1, ⋯, ξ_n) betrachten.")
--
--   **Formalization Note** No non-degeneracy hypothesis is needed or assumed. For $n = 0$ there are no extreme solutions (they are nonzero) and $F = \emptyset$.
--
--   Differences from the source:
--   - encoding: only finitely many extreme solutions, ρξ (ρ > 0) counted as the same solution → a finite set F of extreme solutions such that every extreme solution is ρ • f with f ∈ F and ρ > 0; reason: counting up to positive scaling is a finite set of representatives; same content
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 297, §3 I

import Mathlib
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 I, p. 297: a finite system `S ⊆ ℝⁿ` of inequalities `a ⬝ᵥ ξ ≥ 0` has only
finitely many extreme solutions when positive multiples `ρ ξ` (`ρ > 0`) are regarded as the same
solution: there is a finite set `F` of extreme solutions such that every extreme solution is a
positive multiple of a member of `F`. -/
theorem finite_extreme_solutions {n : ℕ} (S : Finset (Fin n → ℝ)) :
    ∃ F : Finset (Fin n → ℝ), (∀ f ∈ F, IsExtremeSolution S f) ∧
      ∀ ξ : Fin n → ℝ, IsExtremeSolution S ξ → ∃ f ∈ F, ∃ ρ : ℝ, 0 < ρ ∧ ξ = ρ • f := by sorry

end WeylPolyhedra.Polyhedron.Supplement
