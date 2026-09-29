-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_valuation_transEquiv_weilFun
-- name    : WeierstrassCurve.Affine.valuation_transEquiv_weilFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/f1fbd184-0514-54de-a553-6b93eb132cb5
-- title:
--   Valuation of the translated Weil function at finite places
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra and $K$ algebraically closed, let $W$ be an elliptic Weierstrass curve over $F$, and assume the affine coordinate ring of the base change $W⁄K$ is a Dedekind domain. Let $n$ be a natural number whose image in $K$ is nonzero, let $S$ be a point of $W⁄K$, let $T$ be a point with $(n : \mathbb{Z}) \cdot T = 0$, and let $P$ be a point with $P \ne 0$. Write $v_P$ for the valuation on the function field of $W⁄K$ attached to the height-one prime `placeOf W K P hP`, namely the ideal `CoordinateRing.XYIdeal` cut out by the affine coordinates of $P$ (maximal, hence prime, and nonzero). Let $g_T$ be `weilFun W K n T`, the quotient in the function field of the images of `weilNum W K n T` and `weilNum W K n 0`, where `weilNum W K n Q` denotes a chosen generator of `fibIdeal W K n Q` when that ideal is principal and $1$ otherwise, and let `transEquiv W K S` be the $K$-algebra automorphism of the function field given by `transPull W K S`, with inverse `transPull W K (-S)`. Then, in $\mathbb{Z}_{\ge 0}$-valued notation $\operatorname{exp}$ on `WithZero (Multiplicative ℤ)`, $$v_P\bigl(\text{transEquiv } W\, K\, S\,(g_T)\bigr) = \frac{\bigl[\,(n:\mathbb{Z})\cdot(P+S) = T\,\bigr]}{\bigl[\,(n:\mathbb{Z})\cdot(P+S) = 0\,\bigr]},$$ where each bracket denotes $\operatorname{exp}(-1)$ if the stated equality of points holds and $1$ otherwise.
--
--   This is the computation of the divisor of the translate $\tau_S^{*} g_T$ of the Weil function $g_T$ at the finite places of the affine coordinate ring: the order of $g_T \circ \tau_S$ at $P$ is the order of $g_T$ at $P+S$, so that $\tau_S^{*}g_T$ has a simple zero exactly at the points $P$ with $n(P+S) = T$ and a simple pole exactly where $n(P+S) = 0$. It is used in [`WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq`](thm.html#WeierstrassCurve.Affine.exists_transEquiv_weilFun_eq) and thence in the identities `weilPairing0_add_right` and `weilPairing0_self` for the Weil pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_valuation_transEquiv_weilFun.lean

import Mathlib
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.valuation_transEquiv_weilFun {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hn : (n : K) ≠ 0) (S : (W⁄K).Point) {T : (W⁄K).Point} (hT : (n : ℤ) • T = 0) (P : (W⁄K).Point) (hP : P ≠ 0) : (placeOf W K P hP).valuation (W⁄K).FunctionField (transEquiv W K S (weilFun W K n T)) = (if (n : ℤ) • (P + S) = T then exp (-1 : ℤ) else 1) / (if (n : ℤ) • (P + S) = 0 then exp (-1 : ℤ) else 1) := by sorry
