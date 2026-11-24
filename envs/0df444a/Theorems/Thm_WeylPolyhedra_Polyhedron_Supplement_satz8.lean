-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_satz8
-- name    : WeylPolyhedra.Polyhedron.Supplement.satz8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:34:06.497531+00:00
-- url     : https://prove2.me/theorems/dee32108-5a5a-417f-9e71-dabd4e2cec0b
-- title:
--   Satz 8 — $\pi$ is extreme in $(S)$ iff its only decomposition into summands of $(S)$ is the trivial one
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite non-degenerate system of homogeneous inequalities $(a\xi) \ge 0$, $a \in S$, with region $(S)$, and let $\pi \in (S)$. Then $\pi$ is an extreme solution of $S$ if and only if every decomposition of $\pi$ into finitely many summands of $(S)$,
--   $$\pi = \xi^{(1)} + \dots + \xi^{(k)}, \qquad \xi^{(i)} \in (S),$$
--   is trivial, that is, the summands lie on the ray of $\pi$:
--   $$\xi^{(i)} = \rho_i\,\pi \quad (i = 1, \dots, k), \qquad \rho_i \ge 0, \qquad \rho_1 + \dots + \rho_k = 1.$$
--
--   Satz 8 characterizes the extreme solutions by the cone $(S)$ alone, without reference to the inequalities that define it. Weyl uses this in Satz 10 and Satz 11, where the same cone is described by two different systems.
--
--   (Weyl: "Satz 8. π ist in (S) extrem dann und nur dann, wenn die einzige Zerlegung von π in zu (S) gehörige Summanden ξ′ + ξ″ + ⋯ die triviale ist, bei welcher ξ′, ξ″, ⋯ auf demselben Strahl wie π liegen: ξ′_i = ρ′π_i, ξ″_i = ρ″π_i, ⋯ (ρ′ ≧ 0, ρ″ ≧ 0, ⋯; ρ′ + ρ″ + ⋯ = 1).")
--
--   **Formalization Note** Non-degeneracy of $S$ is the standing hypothesis of Satz 4–8, and without it Satz 8 fails: for $S = \{e_1\} \subseteq \mathbb{R}^2$, $\pi = e_2$ is an extreme solution but $e_2 = 2e_2 + (-e_2)$ is a non-trivial decomposition in $(S)$. Decompositions are finite families indexed by $\{1, \dots, k\}$ for any $k \ge 0$. An extreme solution is nonzero by definition; at $\pi = 0$ the right-hand side also fails, because the empty decomposition has $\sum \rho_i = 0 \neq 1$.
--
--   Differences from the source:
--   - encoding: S non-degenerate, stated once in Satz 4 ("Ist S nicht-ausgeartet") and inherited by Satz 5-8 → explicit hypothesis Shared.NonDegenerate S; reason: standing assumption of the section made explicit; it changes no instance of the source's claim
--   - encoding: a decomposition ξ′ + ξ″ + ⋯ of π → a family ξ : Fin k → ℝⁿ for any k : ℕ (k = 0 included) with ∑ ξ i = π; reason: Lean convention for a finite list of summands; at π ≠ 0 the empty family is not a decomposition, and at π = 0 both sides are false, as π = 0 is no ray
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 298, Satz 8

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 II, p. 298, Satz 8: let `S ⊆ ℝⁿ` be a finite non-degenerate system of
inequalities (the standing hypothesis of Satz 4–8) and `π ∈ (S)`. Then `π` is an extreme
solution of `S` if and only if every decomposition `π = ξ′ + ξ″ + ⋯` into finitely many
summands of `(S)` is the trivial one: `ξ^(i) = ρ_i π` with `ρ_i ≥ 0` and `∑ ρ_i = 1`. -/
theorem satz8 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) (π : Fin n → ℝ)
    (hπ : π ∈ solutionRegion S) :
    IsExtremeSolution S π ↔
      ∀ (k : ℕ) (ξ : Fin k → Fin n → ℝ), (∀ i, ξ i ∈ solutionRegion S) → ∑ i, ξ i = π →
        ∃ ρ : Fin k → ℝ, (∀ i, 0 ≤ ρ i) ∧ ∑ i, ρ i = 1 ∧ ∀ i, ξ i = ρ i • π := by sorry

end WeylPolyhedra.Polyhedron.Supplement
