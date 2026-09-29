-- Prove2me | Theorems.Thm_SphericalGeometry_eVariationOn_greatCirclePath
-- name    : SphericalGeometry.eVariationOn_greatCirclePath
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:31:38.624899+00:00
-- url     : https://prove2.me/theorems/f2dc0368-c977-43f8-80a1-5cf7ff053ac7
-- title:
--   A great circle is parametrised by arclength
-- statement:
--   For an orthonormal pair $v_1,v_2$ in a real inner product space, the great circle $\bar c(s)=\cos(s)v_1+\sin(s)v_2$ has total variation exactly $b-a$ on any interval $[a,b]$:
--   $$V_a^b(\bar c)=b-a .$$
--   In other words the great circle is parametrised by arclength, and the length of the arc traced over a parameter interval is the length of that interval, counted with multiplicity when the interval is longer than a full turn.
--
--   **Role.** The length of the image of a circle under a homogeneous harmonic map is claimed, in the constant-distance case, to be exactly $2\pi\alpha L$. Once the image has been identified with the great circle of radius $L$ traversed at speed $\alpha$, that identity is precisely this computation, rescaled. The inequality $\le$ follows from the Lipschitz bound alone; the content here is the matching lower bound, which is what makes the length identity an equality rather than an estimate.
--
--   **The argument.** The upper bound is the Lipschitz estimate: the great circle is $1$-Lipschitz, so its variation on $[a,b]$ is at most $b-a$.
--
--   For the lower bound, write $T=b-a$ and, for each $n\ge1$, take the uniform partition $a,\,a+\frac{T}{n},\dots,b$. Along a great circle the chord between parameters differing by $h$ is $2|\sin(h/2)|$, so the corresponding approximating sum is
--   $$n\cdot 2\left|\sin\frac{T}{2n}\right| ,$$
--   and each such sum is a lower bound for the variation. Writing this as $T\cdot\frac{\sin x_n}{x_n}$ with $x_n=T/(2n)$ — legitimate once $n$ is large enough that $x_n\in(0,\pi)$, so that the sine is positive — and using $\sin x/x\to1$ as $x\to0$, which is the differentiability of the sine at the origin, the sums converge to $T$. Hence $T$ is at most the variation.
-- source:
--   The arclength parametrisation of a great circle; the length of the image of the unit circle in Lemma 3.2 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem eVariationOn_greatCirclePath {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1)
    (ho : inner ℝ v1 v2 = 0) (a b : ℝ) (hab : a ≤ b) :
    eVariationOn (greatCirclePath v1 v2) (Set.Icc a b) = ENNReal.ofReal (b - a) := by sorry

end SphericalGeometry
