-- Prove2me | Theorems.Thm_SphericalGeometry_eq_greatCirclePath_of_inner_eq_cos
-- name    : SphericalGeometry.eq_greatCirclePath_of_inner_eq_cos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:48:00.862322+00:00
-- url     : https://prove2.me/theorems/d1f344fe-d19c-482d-9a50-bba474052b2c
-- title:
--   A locally unit-speed curve on a sphere is locally a great circle
-- statement:
--   Let $E$ be a real inner product space and let $\gamma:\mathbb{R}\to E$ take values in the unit sphere and satisfy
--   $$\langle\gamma(s),\gamma(t)\rangle=\cos(s-t)\qquad\text{whenever }|s-t|\le\delta,$$
--   for some $0<\delta<\pi$; equivalently, the spherical angle between $\gamma(s)$ and $\gamma(t)$ is $|s-t|$ at nearby parameters, so $\gamma$ is a unit-speed curve on the sphere in the local sense. Then $\gamma$ is a great circle near every parameter: for each $s_0$ there is an orthonormal pair $v_1,v_2\in E$ with
--   $$\gamma(s)=\cos(s-s_0)\,v_1+\sin(s-s_0)\,v_2\qquad\text{for all }|s-s_0|\le\delta/2 .$$
--
--   **Role.** This is the rigidity statement that a local geodesic of a round sphere is an arc of a great circle, in the form needed for building geometry: a closed local geodesic in the space of directions of a Euclidean building, which is what the image of the unit circle under a homogeneous harmonic map becomes, is a billiards path, and a billiards path lifts to a unit-speed geodesic of the model sphere. The theorem above is the analytic heart of that lift, isolated from all building-theoretic structure. Combined with the fact that a shift realised by an element of a finite isometry group is a rational multiple of a full turn, it yields the rationality of the order.
--
--   **The argument.** Fix $s_0$ and set $t_0=\delta/2$, so that $0<t_0<\pi$ and $\sin t_0\ne0$. Put $a=\gamma(s_0)$ and $c=\gamma(s_0+t_0)$; the hypothesis gives $\langle a,c\rangle=\cos t_0$. Define
--   $$b=\frac{c-\cos(t_0)\,a}{\sin t_0}.$$
--   Then $\langle a,b\rangle=0$ and $\|b\|=1$, the latter because $\|c-\cos(t_0)a\|^{2}=1-\cos^{2}t_0=\sin^{2}t_0$, and $c=\cos(t_0)a+\sin(t_0)b$.
--
--   Now let $|s-s_0|\le t_0$, so that both $|s-s_0|$ and $|s-(s_0+t_0)|$ are at most $\delta$. The hypothesis gives $\langle\gamma(s),a\rangle=\cos(s-s_0)$ and $\langle\gamma(s),c\rangle=\cos(s-s_0-t_0)$; expanding the second through $c=\cos(t_0)a+\sin(t_0)b$ and using the addition formula for the cosine, the terms in $\cos t_0$ cancel and, dividing by $\sin t_0\ne0$, one gets $\langle\gamma(s),b\rangle=\sin(s-s_0)$. Writing $P=\cos(s-s_0)a+\sin(s-s_0)b$, orthonormality of $a,b$ gives $\|P\|^{2}=1$ and the two computed inner products give $\langle\gamma(s),P\rangle=1$; hence $\|\gamma(s)-P\|^{2}=1-2+1=0$ and $\gamma(s)=P$.
-- source:
--   The fact that a local geodesic of the round sphere is a great-circle arc, and that a billiards path lifts to a unit-speed geodesic of the model sphere, B. Kleiner and B. Leeb, Rigidity of quasi-isometries for symmetric spaces and Euclidean buildings, Publ. Math. IHES 86 (1997), Section 4; used in Section 4 of C. Breiner and B. K. Dees, arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem eq_greatCirclePath_of_inner_eq_cos {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (gamma : ℝ → E) (delta : ℝ) (hdelta : 0 < delta)
    (hdpi : delta < Real.pi) (hnorm : ∀ s : ℝ, ‖gamma s‖ = 1)
    (hinner : ∀ s t : ℝ, |s - t| ≤ delta →
      inner ℝ (gamma s) (gamma t) = Real.cos (s - t))
    (s0 : ℝ) :
    ∃ v1 v2 : E, ‖v1‖ = 1 ∧ ‖v2‖ = 1 ∧ inner ℝ v1 v2 = 0 ∧
      ∀ s : ℝ, |s - s0| ≤ delta / 2 →
        gamma s = greatCirclePath v1 v2 (s - s0) := by sorry

end SphericalGeometry
