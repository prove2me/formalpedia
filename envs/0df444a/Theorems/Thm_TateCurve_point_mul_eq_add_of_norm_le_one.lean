-- Prove2me | Theorems.Thm_TateCurve_point_mul_eq_add_of_norm_le_one
-- name    : TateCurve.point_mul_eq_add_of_norm_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/a666742e-7922-5c80-aa45-1b0da3f9df4a
-- title:
--   Additivity of the Tate parametrisation on the fundamental annulus
-- statement:
--   Let $K$ be a field carrying a non-trivial ultrametric norm, complete, of characteristic zero and algebraically closed (with the routine decidability and instance assumptions), and let $q \in K$ with $q \neq 0$ and $\|q\| < 1$. Write `curve q` for the Weierstrass curve over $K$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (1,0,0,\mathrm{a₄}\,q,\mathrm{a₆}\,q)$, i.e. $y^2 + xy = x^3 + \mathrm{a₄}\,q\,x + \mathrm{a₆}\,q$, and, for a parameter $u \in K$, let `pointX q u` be $\bigl(\sum_{n \in \mathbb{Z}} \mathrm{xfun}(q^n u)\bigr) - 2\,\mathrm{s₁}\,q$ and `pointY q u` be $\bigl(\sum_{n \in \mathbb{Z}} \mathrm{yfun}(q^n u)\bigr) + \mathrm{s₁}\,q$, the Tate series attached to the functions `xfun`, `yfun` and to `s₁`. Let $v, w \in K$ satisfy $\|v\| \le 1$, $\|w\| \le 1$, $\|q\| < \|vw\|$, together with $v \neq 1$, $w \neq 1$ and $vw \neq 1$, and assume that the three pairs $(\mathrm{pointX}\,q\,(v*w), \mathrm{pointY}\,q\,(v*w))$, $(\mathrm{pointX}\,q\,v, \mathrm{pointY}\,q\,v)$ and $(\mathrm{pointX}\,q\,w, \mathrm{pointY}\,q\,w)$ are nonsingular points of the affine curve attached to `curve q`. Then, in the group of points of that affine curve, the affine point with parameter $vw$ equals the sum of the affine points with parameters $v$ and $w$.
--
--   This is the homomorphism property of Tate's uniformisation $K^\times/q^{\mathbb{Z}} \to E_q(K)$, stated for parameters lying in the fundamental annulus $\|q\| < \|u\| \le 1$ of the lattice $q^{\mathbb{Z}}$ and under the hypothesis that the product of the two parameters again lies there; no general-position assumption is made, so duplication and the cases involving $2$-torsion are covered. It is used in the analysis of the Tate points of parameters $c\,q^{j}$ on a Tate curve with parameter a power of $q$, via [`ModularCurve.toricPoint_add_nonToricPoint_of_charZero`](thm.html#ModularCurve.toricPoint_add_nonToricPoint_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_point_mul_eq_add_of_norm_le_one.lean

import Mathlib
import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve WeierstrassCurve.Affine
open scoped NNReal

universe u in

theorem TateCurve.point_mul_eq_add_of_norm_le_one
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K]
    {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {v w : K} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hqvw : ‖q‖ < ‖v * w‖) (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v * w ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ := by sorry
