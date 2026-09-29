-- Prove2me | Theorems.Thm_WeierstrassCurve_mem_valuationSubring_of_equation
-- name    : WeierstrassCurve.mem_valuationSubring_of_equation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/3fb325ed-4ff0-5f26-b86a-e354a476f5e0
-- title:
--   Integral x-coordinate forces integral y-coordinate
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $W$ be a Weierstrass curve over $\mathbb{Z}$, i.e. a tuple of coefficients $a_1,a_2,a_3,a_4,a_6\in\mathbb{Z}$, and let $A$ be a valuation subring of $K$. Write $W_{\mathbb{Q}}$ for the image of $W$ under the ring homomorphism $\mathbb{Z}\to\mathbb{Q}$ and $(W_{\mathbb{Q}})_K$ for its base change along $\mathbb{Q}\to K$. Suppose $x,y\in K$ satisfy the affine Weierstrass equation of $(W_{\mathbb{Q}})_K$, that is $y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6$ with the coefficients read in $K$ via the canonical map $\mathbb{Z}\to K$; only this equation is assumed, no nonsingularity condition. Then if $x\in A$, also $y\in A$. The conclusion is thus that for a point on an integral Weierstrass model over any field of characteristic $0$, integrality of the abscissa at a valuation forces integrality of the ordinate at that valuation.
--
--   This is the standard integrality bookkeeping for points on an integral Weierstrass model: a valuation ring is integrally closed, and $y$ satisfies a monic quadratic over $A$ once $x\in A$. It is used in the study of the local behaviour of a Frey-type curve at a place, being cited in the verification that a point lies in the relevant component at a good prime ([`WeierstrassCurve.inZeroComponentAt_of_isGoodPrimeFor`](thm.html#WeierstrassCurve.inZeroComponentAt_of_isGoodPrimeFor)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_mem_valuationSubring_of_equation.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.mem_valuationSubring_of_equation {K : Type*} [Field K] [Algebra ℚ K] (W : WeierstrassCurve ℤ) (A : ValuationSubring K) {x y : K} (h : ((W.map (Int.castRingHom ℚ))⁄K).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by sorry
