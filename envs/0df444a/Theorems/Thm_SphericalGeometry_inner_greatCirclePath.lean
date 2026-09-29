-- Prove2me | Theorems.Thm_SphericalGeometry_inner_greatCirclePath
-- name    : SphericalGeometry.inner_greatCirclePath
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:14:06.474124+00:00
-- url     : https://prove2.me/theorems/24a07040-d192-441f-8b76-64476de6ca41
-- title:
--   The inner product along a great circle is the cosine of the parameter difference
-- statement:
--   Let $v_1,v_2$ be an orthonormal pair in a real inner product space and let $c(s)=\cos(s)v_1+\sin(s)v_2$ be the great circle through them. Then for all parameters $s,t$,
--
--   $$
--   \bigl\langle c(s),c(t)\bigr\rangle=\cos(s-t).
--   $$
--
--   **Role.** This single identity carries all the metric information of a great circle. Setting $t=s$ gives $\|c(s)\|=1$, so the curve lies on the unit sphere; taking $\arccos$ gives the angle between two of its points, so the parameter is arclength for the angular metric; and setting $t=0$ turns the closing condition $c(T)=c(0)$ into the equation $\cos T=1$, which is what forces a period of a great circle to be an integer multiple of $2\pi$. It is an addition formula in disguise: the expansion of the left-hand side by bilinearity produces $\cos s\cos t+\sin s\sin t$, which is $\cos(s-t)$.
-- source:
--   Standard spherical geometry; the great-circle facts are the content of the lift used in Lemma 4.6 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, Section 4 (Spherical Billiards). Mathlib has no parametrized great circle and no geodesics of a sphere.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

theorem inner_greatCirclePath {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) (s t : ℝ) :
    inner ℝ (greatCirclePath v1 v2 s) (greatCirclePath v1 v2 t) = Real.cos (s - t) := by sorry

end SphericalGeometry
