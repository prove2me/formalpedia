-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_add_right
-- name    : WeierstrassCurve.Affine.weilPairing0_add_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f2e959bd-cbfa-50ec-aa11-c646455687d4
-- title:
--   Additivity of e₀(S,·) in the second variable
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, $K$ algebraically closed, let $W$ be a Weierstrass curve over $F$ that is elliptic, and assume that the coordinate ring of the base change $W\!\mathbin{/\!\!/}K$ is a Dedekind domain. Let $n$ be a natural number with $n \neq 0$ in $K$, and let $S, T, T'$ be points of $(W\!\mathbin{/\!\!/}K)$ each annihilated by $n$, i.e. $(n:\mathbb{Z}) \bullet S = 0$, $(n:\mathbb{Z}) \bullet T = 0$ and $(n:\mathbb{Z}) \bullet T' = 0$. Recall that `weilPairing0 W K n S T` is the unit $c \in K^\times$ selected from a proof that the translation automorphism `transEquiv W K S` of the function field of $W\!\mathbin{/\!\!/}K$ sends `weilFun W K n T` to $c \cdot$ `weilFun W K n T`, where `weilFun W K n T` is the quotient of the images of `weilNum W K n T` and `weilNum W K n 0` in the function field, and is $1$ if no such unit exists. The assertion is the equality of units $$e_0(S, T + T') = e_0(S,T)\, e_0(S,T')$$ for $e_0 =$ `weilPairing0 W K n`.
--
--   This is additivity of the Weil pairing in its second argument (Silverman, AEC III.8, Prop. 8.1(a)), here for the point-level pairing `weilPairing0` built from translation of the functions $g_T$. It is used in the treatment of full-level structures on modular curves, for instance in the level-relabelling results identifying elements of $\Gamma$ by their effect on the pairing and in the determinant computations attached to them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_weilPairing0_add_right.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.weilPairing0_add_right {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (S T T' : (W⁄K).Point) (hS : (n : ℤ) • S = 0) (hT : (n : ℤ) • T = 0) (hT' : (n : ℤ) • T' = 0) : weilPairing0 W K n S (T + T') = weilPairing0 W K n S T * weilPairing0 W K n S T' := by sorry
