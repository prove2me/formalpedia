-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_weilFun_ne_zero
-- name    : WeierstrassCurve.Affine.weilFun_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/999c93b5-5236-5294-9ada-65ba22f44d87
-- title:
--   Nonvanishing of the Weil function g_T for T ∈ E[n]
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, $K$ algebraically closed, and let $W$ be a Weierstrass curve over $F$ which is elliptic, such that the affine coordinate ring of the base change $W⁄K$ is a Dedekind domain. Let $n$ be a natural number whose image in $K$ is nonzero, and let $T$ be a point of $W⁄K$ annihilated by $n$, i.e. $(n : \mathbb{Z}) \bullet T = 0$. The assertion is that the element `weilFun W K n T` of the function field of $W⁄K$ is nonzero. By definition this element is the quotient, in the function field, of the images of `weilNum W K n T` and `weilNum W K n 0` under the map from the coordinate ring, where for an integer $m$ and a point $S$ the element `weilNum W K m S` is a chosen generator of the ideal `fibIdeal W K m S` of the coordinate ring when that ideal is principal, and $1$ otherwise. Thus the conclusion says that the numerator attached to $T$ and the denominator attached to the zero point are both nonzero, so that their ratio is a nonzero element of $K(E)$.
--
--   This is the first step in the construction of the Weil pairing on $n$-torsion: the function $g_T = P_T/P_O$ of Silverman's treatment is a well-defined nonzero element of the function field, so that its divisor and its behaviour under translation and under field automorphisms can be analysed. It is used by the statements comparing `weilFun` along algebra homomorphisms, under translation by torsion points, and under isomorphisms of the underlying curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_weilFun_ne_zero.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.weilFun_ne_zero {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) : weilFun W K n T ≠ 0 := by sorry
