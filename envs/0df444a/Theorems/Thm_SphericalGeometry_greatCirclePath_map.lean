-- Prove2me | Theorems.Thm_SphericalGeometry_greatCirclePath_map
-- name    : SphericalGeometry.greatCirclePath_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T03:08:42.5394+00:00
-- url     : https://prove2.me/theorems/9a1435ad-4b13-42c2-a6b2-f2dbb6baba08
-- title:
--   A linear isometry carries a great circle to the great circle of the image pair
-- statement:
--   For a linear isometry $f$ of a real inner product space and any $v_1,v_2$,
--
--   $$
--   f\bigl(\cos(t)v_1+\sin(t)v_2\bigr)=\cos(t)\,f(v_1)+\sin(t)\,f(v_2),
--   $$
--
--   so $f$ carries the great circle through $(v_1,v_2)$ onto the great circle through $(f(v_1),f(v_2))$, parameter for parameter.
--
--   **Role.** Small but load-bearing. In a Euclidean building two apartment charts overlapping along an arc differ by an element of the affine Weyl group; when both charts are normalized to send the origin to the cone point, that element fixes the origin and is therefore a linear isometry of the model apartment, lying in the finite rotational Weyl group $W$. This identity is what says that the transition then acts on the *data* of the great circle rather than merely on its points: combined with the fact that a great circle is determined by an arbitrarily short arc, it turns an overlap relation between two local descriptions of a curve into the equations $f(u_1)=v_1$, $f(u_2)=v_2$ relating their defining pairs.
--
--   That is the step which makes the local great-circle descriptions of a closed local geodesic in a spherical building transform under $W$, and hence the step which makes the monodromy around the circle a single Weyl element.
-- source:
--   Elementary. Used for the transition between apartment charts in C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, Section 4.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

theorem greatCirclePath_map {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E ≃ₗᵢ[ℝ] E) (v1 v2 : E) (t : ℝ) :
    f (greatCirclePath v1 v2 t) = greatCirclePath (f v1) (f v2) t := by sorry

end SphericalGeometry
