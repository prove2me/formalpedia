-- Prove2me | Theorems.Thm_SubdetDiameter_Polytope_levy_cone_of_revolution_min
-- name    : SubdetDiameter.Polytope.levy_cone_of_revolution_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:05:17.654995+00:00
-- url     : https://prove2.me/theorems/34110304-f81c-4e40-89dc-493fa6802508
-- title:
--   Lemma 4: cones of revolution minimise the lateral surface among spherical cones of equal volume
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a measurable spherical cone, i.e. $S = C \cap B_n$ for a set $C$ closed under multiplication by non-negative scalars, and let $S^*$ be a spherical cone of revolution with axis $v \ne 0$ and angle $0 < \theta \le \pi/2$,
--   $$S^* = \Big\{x \in B_n : \frac{v^T x}{\|v\|\,\|x\|} \ge \cos\theta\Big\}.$$
--   If $\mathrm{vol}(S^*) = \mathrm{vol}(S)$, then
--   $$D(S^*) \le D(S),$$
--   where $D$ denotes the dockable (lateral) surface, the $(n-1)$-dimensional measure of the boundary of the cone inside the open unit ball.
--
--   The paper states this as "the spherical cone of given volume with minimum lateral surface is a cone of revolution"; it is the conical form of Lévy's isoperimetric inequality on the sphere, and reduces the lower bound on $D(S)/\mathrm{vol}(S)$ for arbitrary spherical cones to the cones of revolution.
--
--   **Formalization Note** The minimality claim is stated as an inequality against every admissible competitor: for every measurable spherical cone $S$ and every cone of revolution $S^*$ (in the paper's sense, $0<\theta\le\pi/2$) of the same volume, $D(S^*) \le D(S)$. Existence of a cone of revolution of a prescribed volume is not asserted; since $\theta \le \pi/2$, such cones have at most half the volume of $B_n$, so the statement concerns spherical cones of volume at most $\tfrac12\mathrm{vol}(B_n)$, which is the range in which the paper applies it (Lemma 6). Measurability of $S$ is required, as for Lévy's inequality.
-- source:
--   Bonifas, Di Summa, Eisenbrand, Hähnle, Niemeier, On Sub-determinants and the Diameter of Polyhedra, Discrete Comput Geom 52 (2014) 102–115, DOI 10.1007/s00454-014-9601-x, p. 109, Lemma 4 (cone of revolution defined on p. 109)

import Mathlib
import Definitions.Def_SubdetDiameter_Polytope_sphericalCone

namespace SubdetDiameter.Polytope

theorem levy_cone_of_revolution_min (n : ℕ) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : IsSphericalCone S) (hSm : MeasurableSet S)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ : θ ≤ Real.pi / 2)
    (hvol : MeasureTheory.volume (coneOfRevolution v θ) = MeasureTheory.volume S) :
    dockable (coneOfRevolution v θ) ≤ dockable S := by sorry

end SubdetDiameter.Polytope
