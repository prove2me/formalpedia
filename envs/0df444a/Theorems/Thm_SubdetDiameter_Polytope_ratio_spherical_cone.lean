-- Prove2me | Theorems.Thm_SubdetDiameter_Polytope_ratio_spherical_cone
-- name    : SubdetDiameter.Polytope.ratio_spherical_cone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:06:30.246276+00:00
-- url     : https://prove2.me/theorems/dbc7c2b4-2c5b-45db-8a0c-b52d31e3b2d0
-- title:
--   Lemma 6: $D(S)/\mathrm{vol}(S) \ge \sqrt{2n/\pi}$ for spherical cones of at most half the ball's volume
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a (not necessarily convex) measurable spherical cone, $S = C \cap B_n$ with $C$ closed under multiplication by non-negative scalars, such that
--   $$\mathrm{vol}(S) \le \tfrac12\,\mathrm{vol}(B_n).$$
--   Then its dockable surface satisfies
--   $$\sqrt{\frac{2n}{\pi}}\;\mathrm{vol}(S) \le D(S).$$
--
--   This is inequality (5) of the paper, the lower half of the volume-expansion argument: a union of normal cones covering at most half of the ball must expose a proportionally large surface, which the neighbouring normal cones have to cover.
--
--   **Formalization Note** The paper writes the ratio $D(S)/\mathrm{vol}(S) \ge \sqrt{2n/\pi}$; the Lean statement is the multiplicative form in $[0,\infty]$, which is trivially true when $\mathrm{vol}(S) = 0$. Measurability of $S$ is assumed (the paper's $\mathrm{vol}(S)$ presupposes it). $D$ is `μHE[n-1]` of `frontier S ∩ ball 0 1`.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 111, Lemma 6 (= inequality (5), p. 108)

import Mathlib
import Definitions.Def_SubdetDiameter_Polytope_sphericalCone

namespace SubdetDiameter.Polytope

theorem ratio_spherical_cone (n : ℕ) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : IsSphericalCone S) (hSm : MeasurableSet S)
    (hvol : MeasureTheory.volume S ≤
      (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    ENNReal.ofReal (Real.sqrt (2 * n / Real.pi)) * MeasureTheory.volume S ≤ dockable S := by sorry

end SubdetDiameter.Polytope
