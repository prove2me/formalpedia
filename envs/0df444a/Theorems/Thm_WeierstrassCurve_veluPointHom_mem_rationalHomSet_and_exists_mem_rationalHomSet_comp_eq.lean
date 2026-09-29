-- Prove2me | Theorems.Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
-- name    : WeierstrassCurve.veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/3a07dc99-01be-5d06-a33c-24126e0af938
-- title:
--   Vélu's quotient map is rational and universal
-- statement:
--   Let $F$ be an algebraically closed field and $W$ a Weierstrass curve over $F$ whose discriminant is a unit, let $n\in\mathbb{N}$ and let $Q$ be an affine point of $W$ of exact additive order $2n+1$. Write $S=$ `W.oddOrderSummingSet Q n` for the finite set of coordinate pairs of the multiples $kQ$, $1\le k\le n$ (the zero point contributing $(0,0)$), and let $W/S=$ `W.veluQuotient S` be the curve with the same $a_1,a_2,a_3$ and with $a_4$ replaced by $a_4-5\sum_{P\in S}T_P$ and $a_6$ by $a_6-b_2\sum_{P\in S}T_P-7\sum_{P\in S}w_P$. Let $\varphi\colon W(F)\to (W/S)(F)$ be an additive map on affine points whose kernel is the subgroup of integer multiples of $Q$ and which, at every nonsingular affine point $(x,y)$ not lying in $\langle Q\rangle$, is given by Vélu's formulas: $\varphi(x,y)=\bigl(\,$`W.veluX S x`$,\,$`W.veluY S x y`$\,\bigr)$, where `veluX` adds to $x$ the sum of $T_P/(x-x_P)+U_P/(x-x_P)^2$ over $P\in S$ and `veluY` subtracts from $y$ the corresponding sum of terms with denominators $(x-x_P)^2,(x-x_P)^3$. Then two things hold. First, $\varphi$ lies in `rationalHomSet F W (W.veluQuotient S)`: either $\varphi=0$, or there are bivariate polynomials $n_X,d_X,n_Y,d_Y$ over $F$ and a finite set $B\subseteq F$ such that for every nonsingular affine $(x,y)$ with $x\notin B$ the values $d_X(x,y),d_Y(x,y)$ are nonzero and $\varphi(x,y)=\bigl(n_X(x,y)/d_X(x,y),\,n_Y(x,y)/d_Y(x,y)\bigr)$. Second, for every Weierstrass curve $W_3$ over $F$ with unit discriminant and every additive $\alpha\colon W(F)\to W_3(F)$ lying in `rationalHomSet F W W₃` with $\alpha(Q)=0$, there exists $\beta$ in `rationalHomSet F (W.veluQuotient S) W₃` with $\alpha=\beta\circ\varphi$. (The base change occurring in `rationalHomSet` is along the identity of $F$.)
--
--   This is Vélu's construction of the quotient of an elliptic curve by a cyclic subgroup of odd order, together with the universal property that an isogeny killing that subgroup factors through the quotient (Silverman, Corollary III.4.11), phrased in terms of homomorphisms of $F$-points admitting a rational description. It supplies the supersingular-isogeny input used in the computations with Hecke operators on modular curves in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_RationalEnd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.veluPointHom_mem_rationalHomSet_and_exists_mem_rationalHomSet_comp_eq
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (φ : W.toAffine.Point →+ (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (W.veluX (W.oddOrderSummingSet Q n) x)
          (W.veluY (W.oddOrderSummingSet Q n) x y) h') :
    φ ∈ WeierstrassCurve.rationalHomSet F W (W.veluQuotient (W.oddOrderSummingSet Q n)) ∧
      ∀ (W₃ : WeierstrassCurve F) [W₃.IsElliptic] (α : W.toAffine.Point →+ W₃.toAffine.Point),
        α ∈ WeierstrassCurve.rationalHomSet F W W₃ → α Q = 0 →
          ∃ β ∈ WeierstrassCurve.rationalHomSet F (W.veluQuotient (W.oddOrderSummingSet Q n)) W₃,
            α = β.comp φ := by sorry
