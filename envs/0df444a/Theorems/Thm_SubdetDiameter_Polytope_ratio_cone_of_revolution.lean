-- Prove2me | Theorems.Thm_SubdetDiameter_Polytope_ratio_cone_of_revolution
-- name    : SubdetDiameter.Polytope.ratio_cone_of_revolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:05:42.599337+00:00
-- url     : https://prove2.me/theorems/f56d2d26-868a-42bf-b1d9-edd100beb7af
-- title:
--   Lemma 5: $D(S)/\mathrm{vol}(S) \ge \sqrt{2n/\pi}$ for spherical cones of revolution
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a spherical cone of revolution with axis $v \ne 0$ and angle $0 < \theta \le \pi/2$, that is $S = \{x \in B_n : v^T x \ge \cos\theta\,\|v\|\,\|x\|\}$. Then its dockable surface $D(S)$ and its volume satisfy
--   $$\sqrt{\frac{2n}{\pi}}\;\mathrm{vol}(S) \le D(S).$$
--
--   The extreme case is the half ball ($\theta = \pi/2$), where $D(S)$ is the volume of the $(n-1)$-dimensional unit ball. Combined with Lemma 4 this gives the lower bound on the surface-to-volume ratio of every spherical cone of at most half the ball's volume.
--
--   **Formalization Note** The paper writes the ratio $D(S)/\mathrm{vol}(S) \ge \sqrt{2n/\pi}$; the Lean statement is the multiplicative form in $[0,\infty]$ (here $\mathrm{vol}(S) > 0$ for $n \ge 1$). $D$ is `μHE[n-1]` of `frontier S ∩ ball 0 1`. For $n = 0$ there is no $v \ne 0$, so the statement is vacuous there.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 110, Lemma 5

import Mathlib
import Definitions.Def_SubdetDiameter_Polytope_sphericalCone

namespace SubdetDiameter.Polytope

theorem ratio_cone_of_revolution (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2) :
    ENNReal.ofReal (Real.sqrt (2 * n / Real.pi)) *
        MeasureTheory.volume (coneOfRevolution v θ) ≤
      dockable (coneOfRevolution v θ) := by sorry

end SubdetDiameter.Polytope
