-- Prove2me | Theorems.Thm_SphericalGeometry_greatCirclePath_shift
-- name    : SphericalGeometry.greatCirclePath_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-28T03:12:33.412389+00:00
-- url     : https://prove2.me/theorems/0d02e12e-d8f4-442f-b7f8-995809b09383
-- title:
--   Shifting the parameter of a great circle rotates its defining pair
-- statement:
--   Shifting the parameter of a great circle by a constant $c$ produces the great circle of the rotated pair:
--
--   $$
--   \cos(s+c)\,v_1+\sin(s+c)\,v_2
--   =\cos(s)\bigl(\cos(c)v_1+\sin(c)v_2\bigr)+\sin(s)\bigl(-\sin(c)v_1+\cos(c)v_2\bigr).
--   $$
--
--   **Role.** The family of great circles is closed under reparametrization by translation, and the effect on the data is the rotation of $(v_1,v_2)$ by the angle $c$ within their own plane. This is what allows two descriptions of one curve whose parameters differ by a constant to be compared: after applying the identity, both are great circles in the *same* parameter, so the uniqueness of the defining pair applies and yields equations rather than merely an existence statement.
--
--   It is exactly the situation of a closed curve. If a curve of angular speed $\alpha$ is $2\pi$-periodic, its local description near $\theta_0+2\pi$ is written in the parameter $\alpha\theta+2\pi\alpha$ while the description near $\theta_0$ uses $\alpha\theta$; the identity converts the first into a great circle in $\alpha\theta$ whose pair is the original one rotated by $2\pi\alpha$, and comparing the two is what produces the monodromy relation between the Weyl element of the loop and the rotation by $2\pi\alpha$.
--
--   It also shows that the parametrization of a great circle by arclength is unique only up to a rotation of the frame, which is why the defining pair is data of the parametrized curve rather than of its image.
-- source:
--   Elementary; the addition formulas for sine and cosine. Used to compare local descriptions of a closed curve whose parameters differ by the period, in Section 4 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

theorem greatCirclePath_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (c s : ℝ) :
    greatCirclePath v1 v2 (s + c)
      = greatCirclePath (Real.cos c • v1 + Real.sin c • v2)
          (-(Real.sin c) • v1 + Real.cos c • v2) s := by sorry

end SphericalGeometry
