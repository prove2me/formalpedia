-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_convexHull_eq_extremeSupports
-- name    : WeylPolyhedra.Polyhedron.convexHull_eq_extremeSupports
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:07:39.627274+00:00
-- url     : https://prove2.me/theorems/ae20d679-b45a-4fe5-b3d4-322e12125891
-- title:
--   §4 I: the convex hull of a non-degenerate finite set is cut out by its extreme supports
-- statement:
--   Let $S \subseteq \mathbb{R}^m$ be finite with affine span $\mathbb{R}^m$ (a non-degenerate point system in Weyl's inhomogeneous space $\bar R_{n-1}$, $m = n-1$). Then
--
--   1. $S$ has at least one extreme support $(a, a_0)$, and
--   2. the convex polyhedron $H = \operatorname{conv} S$ is exactly the set of points satisfying all extreme support inequalities of $S$:
--   $$\operatorname{conv} S = \{x \in \mathbb{R}^m : a \cdot x - a_0 \ge 0 \text{ for every extreme support } (a, a_0) \text{ of } S\}.$$
--
--   Here an extreme support is a pair $(a, a_0) \neq (0,0)$ with $a \cdot s - a_0 \ge 0$ on $S$ and equality at $m$ affinely independent points of $S$. This is the "only if" ingredient of §4 II: a convex polyhedron is an intersection of finitely many half-spaces.
--
--   (Weyl: "Darum ist stets eine extreme Stütze vorhanden. … Die durch S darstellbaren Punkte im $\bar R_{n-1}$ bilden die konvexe Hülle H von S, das aus S entspringende „konvexe Polyeder". Es kann durch die endlich vielen extremen Stützungleichungen gekennzeichnet werden.")
--
--   **Formalization Note** Stated in affine form: Weyl's homogeneous point $(x, -1)$ is written $x$, and his support $(\alpha x) \ge 0$ with $\alpha = (a, a_0)$ is $a \cdot x - a_0 \ge 0$. Non-degeneracy of the homogenized system is $\operatorname{aff} S = \mathbb{R}^m$; $n-1$ linearly independent homogenized points are $m$ affinely independent points.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 301, §4 I

import Mathlib
import Definitions.Def_WeylPolyhedra_Polyhedron_Polytope

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §4 I, p. 301, in affine form (`R̄_{n-1} = ℝᵐ`, a point `x` standing for
`(x, -1)`): let `S ⊆ ℝᵐ` be a finite non-degenerate point system (its affine span is the whole
space). Then `S` has at least one extreme support, and the convex hull `H` of `S` — the convex
polyhedron arising from `S` — is characterized by the extreme support inequalities: `H` is the
set of points satisfying `a ⬝ᵥ x - a₀ ≥ 0` for every extreme support `(a, a₀)` of `S`. -/
theorem convexHull_eq_extremeSupports {m : ℕ} (S : Finset (Fin m → ℝ))
    (hS : affineSpan ℝ (S : Set (Fin m → ℝ)) = ⊤) :
    (∃ (a : Fin m → ℝ) (a₀ : ℝ), IsExtremeAffineSupport S a a₀) ∧
      convexHull ℝ (S : Set (Fin m → ℝ)) =
        {x | ∀ (a : Fin m → ℝ) (a₀ : ℝ), IsExtremeAffineSupport S a a₀ → 0 ≤ a ⬝ᵥ x - a₀} := by sorry

end WeylPolyhedra.Polyhedron
