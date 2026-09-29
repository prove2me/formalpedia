-- Prove2me | Theorems.Thm_TateCurve_tateTorsionEquiv_add
-- name    : TateCurve.tateTorsionEquiv_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/aebe8e8a-39a3-589e-a33d-9858e1ffc44d
-- title:
--   Additivity of the Tate curve p-torsion parametrisation
-- statement:
--   Let $K$ be a nontrivially normed field that is ultrametric, complete, of characteristic zero, algebraically closed, and equipped with decidable equality; let $q,\zeta,t\in K$ with $q\neq 0$ and $\|q\|<1$ (in the nonnegative-real norm), let $p$ be a prime with $5\le p$, let $\zeta$ be a primitive $p$-th root of unity and let $t^p=q$. Consider the Weierstrass curve $\mathtt{curve}\ q$ over $K$ with coefficients $(a_1,a_2,a_3,a_4,a_6)=(1,0,0,a_4(q),a_6(q))$ given by the Tate $q$-series, and the bijection `tateTorsionEquiv` from $\mathrm{Fin}\,p\times\mathrm{Fin}\,p$ onto the $\mathbb{Z}$-submodule of points killed by $p$ in the affine point group of this curve, which sends $(i,j)$ to the point $\mathtt{tateTorsionPoint}$ with coordinates $\bigl(\mathrm{pointX}(q,\zeta^i t^j),\mathrm{pointY}(q,\zeta^i t^j)\bigr)$ for $(i,j)\neq(0,0)$ and to $0$ otherwise. The assertion is that for all $a,b\in\mathrm{Fin}\,p\times\mathrm{Fin}\,p$, the underlying curve point attached to $a+b$ (componentwise addition modulo $p$) equals the sum, in the group of affine points, of the points attached to $a$ and to $b$.
--
--   This is the additivity half of the statement that the Tate uniformisation restricts to an isomorphism $\mu_p\times q^{1/p\,\mathbb{Z}}/q^{\mathbb{Z}}\cong E_q[p]$, upgrading the bare bijection `tateTorsionEquiv` to a group-theoretic statement on the underlying points. It is used in the construction of a primitive-root-indexed identification of the $p$-torsion of the Tate curve over an algebraically closed $p$-adic field, and in the analysis of chord and tangent slopes at non-toric points on the modular-curve side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_tateTorsionEquiv_add.lean

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve in

theorem TateCurve.tateTorsionEquiv_add
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {q ζ t : K} (hq0 : q ≠ 0) (hq1 : ‖q‖₊ < 1) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q)
    (a b : Fin p × Fin p) :
    ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht (a + b) :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point)
      = ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht a :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point)
      + ((TateCurve.tateTorsionEquiv q ζ t hq0 hq1 Fact.out hp5 hζ ht b :
        (TateCurve.curve q).n_torsionGen p) : (TateCurve.curve q).toAffine.Point) := by sorry
