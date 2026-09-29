-- Prove2me | Theorems.Thm_SphericalGeometry_greatCirclePath_add
-- name    : SphericalGeometry.greatCirclePath_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T11:17:03.020133+00:00
-- url     : https://prove2.me/theorems/d7914655-99a2-4c40-8543-04a8fac526d2
-- title:
--   Shifting a great circle's parameter rotates its frame
-- statement:
--   Shifting the parameter of a great circle is the same as moving its frame along the circle: for all $s,c$,
--   $$\gamma_{v_1,v_2}(s+c)=\gamma_{\,\gamma_{v_1,v_2}(c),\ \gamma_{v_2,-v_1}(c)}(s).$$
--
--   **Role.** A great circle is named by an orthonormal pair, and the same circle traversed from a different starting point is named by the rotated pair. This identity is the exact statement of that, and it is what turns a shift condition into a condition on frames: an equivariance $\gamma(s+T)=w\cdot\gamma(s)$ holding for all $s$ becomes, by comparing the two named frames, the pair of equations $w v_1=\gamma_{v_1,v_2}(T)$ and $w v_2=\gamma_{v_2,-v_1}(T)$ — that is, $w$ rotates the frame through the angle $T$. This is the bridge between a closed path on the circle and an element of the Weyl group.
--
--   **Proof.** Expand $\cos(s+c)$ and $\sin(s+c)$ by the addition formulas and collect the coefficients of $\cos s$ and $\sin s$: the first is $\cos c\,v_1+\sin c\,v_2=\gamma_{v_1,v_2}(c)$ and the second is $-\sin c\,v_1+\cos c\,v_2=\gamma_{v_2,-v_1}(c)$.
-- source:
--   Elementary identity used in the closed-billiards-path analysis of Section 3 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem greatCirclePath_add {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v1 v2 : E) (c s : ℝ) :
    greatCirclePath v1 v2 (s + c)
      = greatCirclePath (greatCirclePath v1 v2 c)
          (greatCirclePath v2 (-v1) c) s := by sorry

end SphericalGeometry
