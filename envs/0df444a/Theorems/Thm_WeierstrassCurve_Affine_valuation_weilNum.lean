-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_valuation_weilNum
-- name    : WeierstrassCurve.Affine.valuation_weilNum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/010cda30-3345-5c01-a0e7-6d0525ea9d06
-- title:
--   Divisor of `weilNum`: simple zeros on the [n]-fibre over T
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra and $K$ algebraically closed, let $W$ be a Weierstrass curve over $F$ which is elliptic, and write $W⁄K$ for its base change, assumed to have Dedekind affine coordinate ring $(W⁄K).\mathrm{CoordinateRing}$. Let $n$ be a natural number with $(n : K) \neq 0$, let $T$ be a point of $W⁄K$ killed by $n$, i.e. $(n : \mathbb{Z}) \cdot T = 0$, and let $P$ be a point of $W⁄K$ different from the point at infinity. The place `placeOf W K P hP` is the height-one prime of the coordinate ring whose ideal is the ideal $\mathrm{XYIdeal}$ of the affine coordinates $(P.\mathrm{xc}, P.\mathrm{yc})$ of $P$, maximal because those coordinates are nonsingular, and nonzero because the class of $X$ is nonzero. The element `weilNum W K n T` is a chosen generator of the ideal `fibIdeal W K n T` if that ideal is principal, and $1$ otherwise; `fibIdeal W K n T` is the product of the ideals `placeIdeal W K P` over the members of `fibSet W K n T`, the fibre of $[n]$ over $T$, which is finite here, and is $\top$ if that set is infinite. The assertion is that the valuation attached to `placeOf W K P hP` on the function field of $W⁄K$, evaluated on the image of `weilNum W K n T` in the function field, equals $\exp(-1)$ when $(n : \mathbb{Z}) \cdot P = T$, and equals $1$ otherwise; that is, `weilNum W K n T` has a simple zero at each point of the fibre of $[n]$ over $T$ and is a unit at every other affine point.
--
--   This is the divisor computation for the function whose divisor is $\sum_{nP = T} (P) - n^2 (O)$ used in the classical construction of the Weil pairing, as in Silverman III.8; the hypothesis that $T$ is $n$-torsion is what makes the fibre ideal principal, via the divisor-class criterion together with $\sum_{nP=T} P = 0$. It underlies the subsequent statements on valuations of Weil functions and on integral models of the Weil pairing over valuation subrings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_valuation_weilNum.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.valuation_weilNum {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) (P : (W⁄K).Point) (hP : P ≠ 0) : (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (weilNum W K n T)) = if (n : ℤ) • P = T then exp (-1 : ℤ) else 1 := by sorry
