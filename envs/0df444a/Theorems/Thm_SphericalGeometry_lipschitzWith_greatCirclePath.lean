-- Prove2me | Theorems.Thm_SphericalGeometry_lipschitzWith_greatCirclePath
-- name    : SphericalGeometry.lipschitzWith_greatCirclePath
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:17:44.95776+00:00
-- url     : https://prove2.me/theorems/e8d39498-cf89-4446-893c-075cb45a0f3f
-- title:
--   A great circle is a 1-Lipschitz curve
-- statement:
--   For an orthonormal pair $v_1,v_2$ in a real inner product space, the great circle $\bar c(s)=\cos(s)v_1+\sin(s)v_2$ is $1$-Lipschitz:
--   $$\|\bar c(s)-\bar c(t)\|\le|s-t| .$$
--
--   **Role.** The great circle is parametrised by arclength, so its chord distance is at most its arclength; this is the quantitative form of that statement and the constant $1$ is sharp, being attained in the limit of small parameter differences. It gives at once that a great circle arc has finite length, bounded by the angular length of the parameter interval — the upper half of the computation of the length of the image of a circle under a homogeneous harmonic map — and it makes the curve continuous, which is needed before any variational or limiting argument can be applied to it.
--
--   **The argument.** The chord along a great circle is $\|\bar c(s)-\bar c(t)\|=2\bigl|\sin\frac{s-t}{2}\bigr|$, and $|\sin x|\le|x|$ for every real $x$; applying this with $x=(s-t)/2$ gives the bound $2\cdot\frac{|s-t|}{2}=|s-t|$.
-- source:
--   The arclength parametrisation of a great circle; used to bound the length of the image of the unit circle in C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, arXiv:2604.16608, Lemma 3.2.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem lipschitzWith_greatCirclePath {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1)
    (ho : inner ℝ v1 v2 = 0) :
    LipschitzWith 1 (greatCirclePath v1 v2) := by sorry

end SphericalGeometry
