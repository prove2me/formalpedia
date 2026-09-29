-- Prove2me | Theorems.Thm_WeylPolyhedra_Pyramid_hauptsatz_no_extreme_support
-- name    : WeylPolyhedra.Pyramid.hauptsatz_no_extreme_support
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:17:23.106852+00:00
-- url     : https://prove2.me/theorems/4972615f-7715-4f6a-a632-c3f813cd90a8
-- title:
--   §1, p. 291 — case b): with no extreme support, every point is representable
-- statement:
--   Let $S \subset \mathbb{R}^n$ be a finite non-degenerate point system that has no extreme support at all. Then every point of $\mathbb{R}^n$ is a nonnegative linear combination of the points of $S$:
--
--   $$\forall x \in \mathbb{R}^n \quad \exists\, c_s \ge 0 \ (s \in S): \qquad x = \sum_{s \in S} c_s\, s .$$
--
--   This is the special case of the Hauptsatz that Weyl singles out on p. 291 and treats separately in §2 b) (pp. 293–294): in the homogeneous space it can happen that $S$ has no extreme support, and then the condition "all extreme support inequalities hold" is empty, so the Hauptsatz asserts that $S$ generates the whole space as a cone.
--
--   **Formalization Note** Same conventions as the Hauptsatz: $S$ is a `Finset` of vectors in $\mathrm{Fin}\,n \to \mathbb{R}$, non-degeneracy is stated literally, and "no extreme support" means no nonzero normal $\alpha$ satisfies `IsExtremeSupport S α`.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 291, §1 (case b), proved in §2 b), pp. 293–294)

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §1, p. 291 (case b) of the Hauptsatz, proved in §2 b), pp. 293–294): if a finite
non-degenerate point system `S ⊆ ℝⁿ` has no extreme support at all, then every point of `ℝⁿ` is
a nonnegative linear combination of the points of `S`. -/
theorem hauptsatz_no_extreme_support {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hnone : ∀ α : Fin n → ℝ, ¬ Shared.IsExtremeSupport S α) (x : Fin n → ℝ) :
    Shared.Representable S x := by sorry

end WeylPolyhedra.Pyramid
