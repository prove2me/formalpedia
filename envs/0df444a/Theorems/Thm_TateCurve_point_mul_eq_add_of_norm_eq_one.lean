-- Prove2me | Theorems.Thm_TateCurve_point_mul_eq_add_of_norm_eq_one
-- name    : TateCurve.point_mul_eq_add_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/fd83d4f1-73ba-59ac-9ef8-ccfc945a0ce6
-- title:
--   Additivity of Tate's parametrisation on the unit circle
-- statement:
--   Let $K$ be a nontrivially normed field whose norm is ultrametric, complete, of characteristic zero, algebraically closed (and with decidable equality), and let $q \in K$ satisfy $q \neq 0$ and $\lVert q \rVert < 1$ as a nonnegative real. Write `curve q` for the Weierstrass curve over $K$ with coefficients $a_1 = 1$, $a_2 = a_3 = 0$ and $a_4 =$ `a₄ q`, $a_6 =$ `a₆ q`, and for $u \in K$ write `pointX q u` $= \bigl(\sum_{n \in \mathbb{Z}} \mathtt{xfun}(q^n u)\bigr) - 2\,\mathtt{s₁}\,q$ and `pointY q u` $= \bigl(\sum_{n \in \mathbb{Z}} \mathtt{yfun}(q^n u)\bigr) + \mathtt{s₁}\,q$, the coordinate functions assembled from the $q$-series `xfun`, `yfun` and `s₁`. Let $v, w \in K$ have $\lVert v \rVert = \lVert w \rVert = 1$ and satisfy $v \neq 1$, $w \neq 1$, $vw \neq 1$, and assume that the three pairs $(\mathtt{pointX}\,q\,(vw), \mathtt{pointY}\,q\,(vw))$, $(\mathtt{pointX}\,q\,v, \mathtt{pointY}\,q\,v)$ and $(\mathtt{pointX}\,q\,w, \mathtt{pointY}\,q\,w)$ are nonsingular points of the affine curve associated with `curve q`. Then, in the group of points of that affine curve, the affine point attached to $vw$ equals the sum of the affine points attached to $v$ and to $w$. No general-position condition is imposed: the case $w = v$ and the cases where one of the three points is $2$-torsion are included.
--
--   This is the homomorphism property of Tate's uniformisation $K^\times/q^{\mathbb{Z}} \to E_q(K)$, restricted to the unit circle $\lVert u \rVert = 1$, on which the class of $u$ modulo $q^{\mathbb{Z}}$ is trivial exactly when $u = 1$. It is used to show that the toric points of the Tate curve in characteristic zero add correctly, via [`ModularCurve.toricPoint_add_toricPoint_of_charZero`](thm.html#ModularCurve.toricPoint_add_toricPoint_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_point_mul_eq_add_of_norm_eq_one.lean

import Mathlib
import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve WeierstrassCurve.Affine
open scoped NNReal

universe u in

theorem TateCurve.point_mul_eq_add_of_norm_eq_one
    {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K]
    {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) {v w : K} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (hvw : v * w ≠ 1)
    (h₁ : (curve q).toAffine.Nonsingular (pointX q (v * w)) (pointY q (v * w)))
    (h₂ : (curve q).toAffine.Nonsingular (pointX q v) (pointY q v))
    (h₃ : (curve q).toAffine.Nonsingular (pointX q w) (pointY q w)) :
    (Point.some (pointX q (v * w)) (pointY q (v * w)) h₁ : (curve q).toAffine.Point)
      = Point.some (pointX q v) (pointY q v) h₂ + Point.some (pointX q w) (pointY q w) h₃ := by sorry
