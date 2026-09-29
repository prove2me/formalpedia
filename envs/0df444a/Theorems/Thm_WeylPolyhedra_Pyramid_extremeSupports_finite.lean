-- Prove2me | Theorems.Thm_WeylPolyhedra_Pyramid_extremeSupports_finite
-- name    : WeylPolyhedra.Pyramid.extremeSupports_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:15:28.589303+00:00
-- url     : https://prove2.me/theorems/7a44e3f9-83e7-4b02-a365-975c5a96c446
-- title:
--   §1, p. 291 — a finite non-degenerate point system has finitely many extreme supports
-- statement:
--   Let $S \subset \mathbb{R}^n$ be a finite, non-degenerate point system. Then $S$ has only finitely many extreme supports, where two normals that are positive multiples of each other are counted as the same support. Precisely, there is a finite set $F$ of extreme supports of $S$ such that
--
--   $$\text{for every extreme support } \alpha \text{ of } S \text{ there are } \beta \in F,\ c > 0 \text{ with } \alpha = c\,\beta .$$
--
--   Weyl adds how to find them: choose $n-1$ linearly independent points of $S$ in every possible way, pass through them the uniquely determined hyperplane $\langle \alpha, x\rangle = 0$, and test whether one of the two half-spaces $\pm\langle \alpha, x\rangle \ge 0$ is a support.
--
--   The finiteness is what lets the proof of the Hauptsatz take the smallest of the ratios $\langle\alpha,p\rangle/\langle\alpha,e\rangle$ over all extreme supports $\alpha$.
--
--   **Formalization Note** Supports are represented by their normal vectors, so "finitely many supports" is stated up to positive scaling. The search procedure is the proof, not part of the statement.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 291, §1 ("Es existieren nur endlich viele extreme Stützen an S")

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §1, p. 291: a finite non-degenerate point system `S ⊆ ℝⁿ` has only finitely
many extreme supports, counted up to positive scaling (positive multiples of a normal give the
same half-space, p. 291): there is a finite set `F` of extreme supports of `S` such that every
extreme support of `S` is a positive multiple of a member of `F`. -/
theorem extremeSupports_finite {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) :
    ∃ F : Finset (Fin n → ℝ), (∀ β ∈ F, Shared.IsExtremeSupport S β) ∧
      ∀ α, Shared.IsExtremeSupport S α → ∃ β ∈ F, ∃ c : ℝ, 0 < c ∧ α = c • β := by sorry

end WeylPolyhedra.Pyramid
