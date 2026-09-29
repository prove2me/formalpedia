-- Prove2me | Theorems.Thm_TateCurve_tpow_succ_point_eq_add
-- name    : TateCurve.tpow_succ_point_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/e99bc290-dede-5247-826d-b47d597582ea
-- title:
--   Additivity of the Tate parametrisation along powers of t
-- statement:
--   Let $K$ be a complete, algebraically closed, nontrivially normed field of characteristic zero whose norm is ultrametric, and let $q,\zeta,t \in K$ with $q \neq 0$ and $\|q\|_{\mathbb{R}_{\geq 0}} < 1$. Let $p$ be a prime with $p \geq 5$, suppose $\zeta$ is a primitive $p$-th root of unity and $t^{p} = q$, and let $j$ be a natural number with $1 \leq j$ and $j + 1 < p$. Here [`TateCurve.curve q`](def/TateCurve_QSeries.html#L185) is the Weierstrass curve over $K$ with coefficients $a_1 = 1$, $a_2 = a_3 = 0$ and $a_4 =$ `a₄ q`, $a_6 =$ `a₆ q`, and for a parameter $u \in K$ the coordinates are $\mathrm{pointX}(q,u) = \bigl(\sum_{n \in \mathbb{Z}} \mathrm{xfun}(q^{n}u)\bigr) - 2\,s_1(q)$ and $\mathrm{pointY}(q,u) = \bigl(\sum_{n \in \mathbb{Z}} \mathrm{yfun}(q^{n}u)\bigr) + s_1(q)$, the sums being the unconditional sums over $\mathbb{Z}$. Assume the three pairs $(\mathrm{pointX}(q,u),\mathrm{pointY}(q,u))$ for $u = t^{j+1}$, $u = t$ and $u = t^{j}$ are nonsingular points of the associated affine curve, with witnesses $h_1$, $h_2$, $h_3$. Then in the group of points of that affine curve the point attached to the parameter $t^{j+1}$ equals the sum of the points attached to $t$ and to $t^{j}$.
--
--   This is the additivity of the Tate parametrisation $K^{\times}/q^{\mathbb{Z}} \to E_q(K)$ restricted to the powers of a fixed $p$-th root $t$ of $q$, in the form $\varphi(t^{j+1}) = \varphi(t) + \varphi(t^{j})$ (cf. Silverman, Theorem V.3.1). It serves as the inductive step for [`TateCurve.tateTorsionPoint_snd_eq_nsmul`](thm.html#TateCurve.tateTorsionPoint_snd_eq_nsmul), which identifies the point attached to $t^{j}$ with $j$ times the point attached to $t$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_tpow_succ_point_eq_add.lean

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in

theorem TateCurve.tpow_succ_point_eq_add
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    {j : ℕ} (hj1 : 1 ≤ j) (hjp : j + 1 < p)
    (h₁ : (TateCurve.curve q).toAffine.Nonsingular
      (TateCurve.pointX q (t ^ (j + 1))) (TateCurve.pointY q (t ^ (j + 1))))
    (h₂ : (TateCurve.curve q).toAffine.Nonsingular (TateCurve.pointX q t) (TateCurve.pointY q t))
    (h₃ : (TateCurve.curve q).toAffine.Nonsingular
      (TateCurve.pointX q (t ^ j)) (TateCurve.pointY q (t ^ j))) :
    (WeierstrassCurve.Affine.Point.some (TateCurve.pointX q (t ^ (j + 1)))
        (TateCurve.pointY q (t ^ (j + 1))) h₁ : (TateCurve.curve q).toAffine.Point)
      = WeierstrassCurve.Affine.Point.some (TateCurve.pointX q t) (TateCurve.pointY q t) h₂
        + WeierstrassCurve.Affine.Point.some (TateCurve.pointX q (t ^ j))
            (TateCurve.pointY q (t ^ j)) h₃ := by sorry
