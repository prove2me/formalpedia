-- Prove2me | Theorems.Thm_SphericalGeometry_dist_greatCirclePath
-- name    : SphericalGeometry.dist_greatCirclePath
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:09:13.340284+00:00
-- url     : https://prove2.me/theorems/9b1e6bcf-4408-4c1a-b783-7718c2187ea1
-- title:
--   The chord length along a great circle
-- statement:
--   For an orthonormal pair $v_1,v_2$ in a real inner product space, the great circle $\bar c(s)=\cos(s)v_1+\sin(s)v_2$ satisfies
--   $$\bigl\|\bar c(s)-\bar c(t)\bigr\|=2\left|\sin\frac{s-t}{2}\right| .$$
--
--   **Role.** This converts the intrinsic (angular) parameter of a great circle into the ambient chord distance, and is what lets one compare the two metrics on the unit sphere: the chord metric of the ambient space and the angle. It is needed whenever a spherical statement — a curve is a great circle, two points subtend a given angle — has to be turned into an estimate on distances, for instance when the image of a circle under a homogeneous harmonic map is compared with a great circle inside an apartment, or when the length of such an image is estimated.
--
--   **The argument.** The great circle takes values in the unit sphere and satisfies $\langle\bar c(s),\bar c(t)\rangle=\cos(s-t)$. Hence
--   $$\|\bar c(s)-\bar c(t)\|^{2}=1-2\cos(s-t)+1=2-2\cos(s-t),$$
--   and the half-angle identity $\cos x=1-2\sin^{2}(x/2)$ turns the right-hand side into $4\sin^{2}\frac{s-t}{2}$. Both sides of the asserted identity being nonnegative, taking square roots gives the absolute value of the sine.
-- source:
--   The relation between the chord and the arc on a round sphere; standard, and used to compare the angle metric of the space of directions with the ambient metric in B. Kleiner and B. Leeb, Publ. Math. IHES 86 (1997), Section 4.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem dist_greatCirclePath {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) (s t : ℝ) :
    dist (greatCirclePath v1 v2 s) (greatCirclePath v1 v2 t)
      = 2 * |Real.sin ((s - t) / 2)| := by sorry

end SphericalGeometry
