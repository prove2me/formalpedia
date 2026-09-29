-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_valuation_transEquiv_le
-- name    : WeierstrassCurve.Affine.valuation_transEquiv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/ad31d186-5c24-5816-927f-6dcd74404a24
-- title:
--   Translation pull-back does not decrease order of vanishing
-- statement:
--   Let $R$ be a field, $W$ a Weierstrass curve over $R$, and $K$ a field which is an $R$-algebra, assumed algebraically closed, with $W$ elliptic and the coordinate ring of the affine base change $W⁄K$ a Dedekind domain. Let $P$ and $S$ be points of $(W⁄K)$, both different from the point at infinity, with $P.\mathrm{xc} \neq S.\mathrm{xc}$ (distinct $x$-coordinates, so $P \neq \pm S$) and $P + S \neq 0$. For a point $Q \neq 0$, `placeOf W K Q` denotes the height-one prime of the coordinate ring of $W⁄K$ cut out by the ideal `CoordinateRing.XYIdeal` at $(Q.\mathrm{xc}, Q.\mathrm{yc})$, which is maximal, hence prime, and nonzero. Let $h$ be an element of the function field of $W⁄K$ and $k$ a natural number. The assertion is: if the adic valuation of $h$ at `placeOf W K (P + S) hPS` is at most $\exp(-k)$ in $\mathbb{Z}_{m0}$, then the adic valuation of $(\mathrm{transEquiv}\ W\ K\ S)\,h$ at `placeOf W K P hP` is at most $\exp(-k)$; here `transEquiv W K S` is the $K$-algebra automorphism of the function field built from `transPull W K S` with inverse `transPull W K (-S)`, the pull-back along translation by $S$. Equivalently, $\operatorname{ord}_P(h \circ \tau_S) \geq \operatorname{ord}_{P+S}(h)$.
--
--   This records how orders of vanishing transform under the pull-back by translation on the function field of an elliptic curve: a function vanishing to order at least $k$ at $P+S$ pulls back to one vanishing to order at least $k$ at $P$ (equality in fact holds, the translation being an automorphism, but only the inequality is asserted). It is used in the construction and verification of the properties of the Weil pairing, in particular by [`WeierstrassCurve.Affine.valuation_transEquiv_weilFun`](thm.html#WeierstrassCurve.Affine.valuation_transEquiv_weilFun).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_valuation_transEquiv_le.lean

import Mathlib
import Definitions.Def_EllipticCurve_FunctionFieldPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

theorem WeierstrassCurve.Affine.valuation_transEquiv_le {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {P S : (W⁄K).Point} (hP : P ≠ 0) (hS : S ≠ 0) (hx : P.xc ≠ S.xc) (hPS : P + S ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ) (hh : (placeOf W K (P + S) hPS).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) : (placeOf W K P hP).valuation (W⁄K).FunctionField (transEquiv W K S h) ≤ exp (-(k : ℤ)) := by sorry
