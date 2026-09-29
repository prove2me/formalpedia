-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_valuation_placeOf_neg_transEquiv_algebraMap
-- name    : WeierstrassCurve.Affine.valuation_placeOf_neg_transEquiv_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/e721d9e0-49fd-5066-b904-fd5dea90e9bb
-- title:
--   Translation by S moves the place at infinity to -S
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, $K$ algebraically closed and equipped with decidable equality, and let $W$ be a Weierstrass curve over $F$ which is elliptic; assume the affine coordinate ring of the base change $W⁄K$ is a Dedekind domain. Let $S$ be a point of $W⁄K$ with $S \neq 0$, and let $a$ be a nonzero element of the coordinate ring $(W⁄K)$`.CoordinateRing`. Since $-S \neq 0$, the point $-S$ has affine coordinates, and `placeOf W K (-S)` is the height-one prime of the coordinate ring given by the ideal $\mathrm{XYIdeal}$ generated at $(x(-S), y(-S))$, whose primality comes from the maximality of that ideal at a nonsingular point and which is nonzero because the class of $x - x(-S)$ is nonzero. The assertion is that the associated normalised valuation of the function field $(W⁄K)$`.FunctionField`, with values in $\mathbb{Z}$ written multiplicatively with zero, takes on the image of $a$ under the $K$-algebra automorphism `transEquiv W K S` (pull-back along translation by $S$, built from `transPull W K S` and `transPull W K (-S)` as mutually inverse maps) the value $\exp\bigl(\deg_{\mathrm{nat}} N(a)\bigr)$, where $N$ is the norm of the coordinate ring over $K[x]$.
--
--   This is the statement that pull-back along translation by $S$ identifies the place of $-S$ with the place at infinity, at which a polynomial function $a$ has a pole of order $\deg N(a)$; in the normalisation used here the valuation is $\exp$ of minus the order of vanishing. It feeds the computation of the valuation at $-S$ of the translated Weil functions, [`WeierstrassCurve.Affine.valuation_transEquiv_weilFun`](thm.html#WeierstrassCurve.Affine.valuation_transEquiv_weilFun).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_valuation_placeOf_neg_transEquiv_algebraMap.lean

import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.Affine.valuation_placeOf_neg_transEquiv_algebraMap {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] (S : (W⁄K).Point) (hS : S ≠ 0) {a : (W⁄K).CoordinateRing} (ha : a ≠ 0) : (placeOf W K (-S) (neg_ne_zero.mpr hS)).valuation (W⁄K).FunctionField (transEquiv W K S (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField a)) = WithZero.exp ((Algebra.norm (Polynomial K) a).natDegree : ℤ) := by sorry
