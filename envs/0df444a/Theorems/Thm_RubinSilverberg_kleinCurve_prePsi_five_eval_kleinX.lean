-- Prove2me | Theorems.Thm_RubinSilverberg_kleinCurve_prePsi_five_eval_kleinX
-- name    : RubinSilverberg.kleinCurve_prePsi_five_eval_kleinX
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/d4088fcd-e1ad-5705-9de5-af1a4955b993
-- title:
--   Klein's curve: preΨ₅ vanishes at x₀(u)
-- statement:
--   Let $K$ be a field of characteristic zero and let $u \in K$ be arbitrary. Put
--   $$H(u)=u^{20}-228u^{15}+494u^{10}+228u^{5}+1, \qquad T(u)=u^{30}+522u^{25}-10005u^{20}-10005u^{10}-522u^{5}+1,$$
--   and let $\mathtt{kleinCurve}\,u$ be the Weierstrass curve over $K$ with coefficients $a_1=a_2=a_3=0$, $a_4=-H(u)/48$ and $a_6=T(u)/864$, i.e. the curve $y^{2}=x^{3}-\frac{H(u)}{48}x+\frac{T(u)}{864}$. Let
--   $$x_0(u)=\frac{u^{10}+12u^{8}-12u^{7}+24u^{6}+30u^{5}+60u^{4}+36u^{3}+24u^{2}+12u+1}{12}\in K.$$
--   The assertion is that the univariate polynomial $\mathrm{pre}\Psi'_5$ of this curve — Mathlib's normalised $5$-division polynomial in $x$ alone — takes the value $0$ at $x_0(u)$. Thus $x_0(u)$ is a root of the $5$-division polynomial of $\mathtt{kleinCurve}\,u$, identically in $u$ and over every field of characteristic zero.
--
--   This is the computational core of the statement that the point with abscissa $x_0(u)$ on Klein's level-$5$ curve is a $5$-torsion point, the section used by Rubin and Silverberg to realise a family of elliptic curves with constant mod $5$ representation. It is cited by [`RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul`](thm.html#RubinSilverberg.pt_kleinCurve_ne_zero_and_five_smul), which upgrades it to the existence of a point of exact order $5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_kleinCurve_prePsi_five_eval_kleinX.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.kleinCurve_prePsi_five_eval_kleinX {K : Type*} [Field K] [CharZero K] (u : K) : ((kleinCurve u).preΨ' 5).eval (kleinX u) = 0 := by sorry
