-- Prove2me | Theorems.Thm_TateCurve_pointY_inv
-- name    : TateCurve.pointY_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/d92f80c6-6461-5f00-9cfb-ea606d898617
-- title:
--   Inversion formula for the Y-coordinate of the Tate parametrisation
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $q, u \in K$ satisfy: $q \neq 0$, $\|q\| < 1$ (as non-negative reals), $u \neq 0$, and $q^n u \neq 1$ for every $n \in \mathbb{Z}$, i.e. $u$ lies in no $q$-translate of $1$. Here $\mathrm{pointX}(q,u)$ is defined as $\sum_{n \in \mathbb{Z}} \mathrm{xfun}(q^n u) - 2 s_1(q)$ and $\mathrm{pointY}(q,u)$ as $\sum_{n \in \mathbb{Z}} \mathrm{yfun}(q^n u) + s_1(q)$, the sums being unconditional sums over $\mathbb{Z}$ of the termwise series $\mathrm{xTerm}$, $\mathrm{yTerm}$. The conclusion is the identity
--   $$\mathrm{pointY}(q, u^{-1}) = -\,\mathrm{pointY}(q,u) - \mathrm{pointX}(q,u),$$
--   an equality of elements of $K$ between the $Y$-coordinate at the inverse parameter $u^{-1}$ and the expression $-Y - X$ in the coordinates at $u$.
--
--   This is the $Y$-component of the statement that the Tate parametrisation turns inversion in $K^\times/q^{\mathbb{Z}}$ into negation on the Tate curve, negation on the Weierstrass model $y^2 + xy = x^3 + a_4 x + a_6$ being $-(x,y) = (x, -y-x)$. Together with the companion identity for the $X$-coordinate it feeds the exported interface of the Tate-curve series package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_pointY_inv.lean

import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.pointY_inv {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointY q u⁻¹ = -pointY q u - pointX q u := by sorry
