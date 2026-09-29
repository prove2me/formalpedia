-- Prove2me | Theorems.Thm_TateCurve_equation_pointX_pointY
-- name    : TateCurve.equation_pointX_pointY
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/61bc5547-25ab-55fb-bdb4-c450953f70d8
-- title:
--   Tate parametrisation satisfies the Weierstrass equation
-- statement:
--   Let $K$ be a nontrivially normed field of characteristic zero whose norm is ultrametric and which is complete, and let $q, u \in K$ satisfy $q \neq 0$, $\|q\| < 1$ (as nonnegative reals), $u \neq 0$, and $q^{n} u \neq 1$ for every integer $n$. Write $X =$ `pointX q u` for the sum of the family $n \mapsto$ `xfun`$(q^{n} u)$ over $n \in \mathbb{Z}$, minus $2\,$`s₁ q`, and $Y =$ `pointY q u` for the sum of the family $n \mapsto$ `yfun`$(q^{n} u)$ over $n \in \mathbb{Z}$, plus `s₁ q`; here the sums are unconditional sums in $K$ of the term functions `xTerm q u` and `yTerm q u`, and `s₁ q`, `a₄ q`, `a₆ q` are the coefficient series attached to $q$. The conclusion is the identity
--   $$Y^{2} + X Y = X^{3} + \mathtt{a₄}\,q \cdot X + \mathtt{a₆}\,q$$
--   in $K$, that is, the point $(X, Y)$ produced from $u$ by the Tate series lies on the Tate curve with coefficients $a_4(q), a_6(q)$.
--
--   This is the assertion that the Tate parametrisation lands on the Tate curve, the algebraic heart of the rigid-analytic uniformisation $K^{\times}/q^{\mathbb{Z}} \cong E_q(K)$ (Silverman, Theorem V.3.1(a)). It is used to equip points coming from the Tate parametrisation with Weierstrass-equation membership, in particular by [`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation) and [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_equation_pointX_pointY.lean

import Definitions.Def_TateCurve_Defect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.equation_pointX_pointY {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointY q u ^ 2 + pointX q u * pointY q u = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by sorry
