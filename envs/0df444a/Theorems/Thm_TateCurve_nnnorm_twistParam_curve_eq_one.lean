-- Prove2me | Theorems.Thm_TateCurve_nnnorm_twistParam_curve_eq_one
-- name    : TateCurve.nnnorm_twistParam_curve_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/47b7c6b5-3160-560c-b308-0589bae278a4
-- title:
--   Twist parameter against the Tate curve is a unit
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric and which is complete, and let $E$ be a Weierstrass curve over $K$ whose invariants satisfy $\|c_4(E)\|=1$ and $\|\Delta(E)\|<1$ for the multiplicative norm $\|\cdot\|$ (taken with values in $\mathbb{R}_{\ge 0}$). Let $q\in K$ be nonzero with $\|q\|<1$, and let `curve q` be the Weierstrass curve with coefficients $(a_1,a_2,a_3,a_4,a_6)=(1,0,0,a_4(q),a_6(q))$, where $a_4(q)$ and $a_6(q)$ are the $q$-series coefficients of the Tate curve attached to $q$. The assertion is that the quantity
--   $$\left\| \frac{c_6(E)\,c_4(\mathrm{curve}\,q)}{c_6(\mathrm{curve}\,q)\,c_4(E)} \right\| = 1,$$
--   that is, the element $c_6(E)c_4(E_q)/\bigl(c_6(E_q)c_4(E)\bigr)$ of $K$ has norm exactly $1$.
--
--   The displayed quotient is the twisting parameter comparing a Weierstrass curve with unit $c_4$ and nonunit discriminant to the Tate curve of parameter $q$; its being a unit is the quantitative form of the statement that such a curve becomes isomorphic to the Tate curve over an unramified quadratic extension. It is used in [`WeierstrassCurve.exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer`](thm.html#WeierstrassCurve.exists_variableChange_tateCurve_galois_signBehavior_of_stabilizer), where the Tate curve's inertia filtration is transported to a curve of multiplicative reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_nnnorm_twistParam_curve_eq_one.lean

import Definitions.Def_TateCurve_QSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve NNReal
open scoped NNReal
namespace TateCurve
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem nnnorm_twistParam_curve_eq_one (E : WeierstrassCurve K)
    (hc₄ : ‖E.c₄‖₊ = 1) (hΔ : ‖E.Δ‖₊ < 1) {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    ‖E.c₆ * (curve q).c₄ / ((curve q).c₆ * E.c₄)‖₊ = 1 := by sorry
