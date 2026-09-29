-- Prove2me | Theorems.Thm_WeierstrassCurve_heq_fullKernelHom_vcInvFun
-- name    : WeierstrassCurve.heq_fullKernelHom_vcInvFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/959057e5-4321-539e-aab4-1772bee019c9
-- title:
--   Vélu's isogeny commutes with a change of Weierstrass coordinates
-- statement:
--   Let $F$ be a field with decidable equality, $W$ a Weierstrass curve over $F$, $C=(u,r,s,t)$ a change of Weierstrass coordinates, $Q$ an affine point of $W$ and $N$ a natural number with $\mathrm{addOrderOf}\,Q=N$. Write $Q'=$ `Point.vcInvFun C W.toAffine Q`, the image of $Q$ under the substitution sending $0$ to $0$ and $(x,y)$ to $(u^{-2}(x-r),\,u^{-3}(y-t-s(x-r)))$, a point of $C\cdot W$. For a point $R$ of order $N$ on a curve $V$, `V.fullKernelQuotient R N` is the curve with the same $a_1,a_2,a_3$ and with $a_4$ replaced by $a_4-5t_0$ and $a_6$ by $a_6-b_2t_0-7w_0$, where $t_0$ and $w_0$ are the sums of $g_x=3x^2+2a_2x+a_4-a_1y$ and of $xg_x-yg_y$ (with $g_y=-(2y+a_1x+a_3)$) over the set of coordinate pairs $(k\cdot R)$, $1\le k\le N-1$ (the origin contributing $(0,0)$). Assume given additive maps $\varphi$ from the points of $W$ to those of `W.fullKernelQuotient Q N` and $\varphi'$ from the points of $C\cdot W$ to those of `(C • W).fullKernelQuotient Q' N`, each with kernel the subgroup of integer multiples of $Q$, respectively $Q'$, and each satisfying, off that subgroup, the translation-sum formulae $x(\varphi P)=x(P)+\sum_{k=1}^{N-1}(x(P+kQ)-x(kQ))$ and $y(\varphi P)=y(P)+\sum_{k=1}^{N-1}(y(P+kQ)-y(kQ))$ (and likewise for $\varphi'$ with $Q'$), coordinates being read via `coordsOrZero`. Then for every point $P$ of $W$ one has the heterogeneous equality of $\varphi'$ applied to the transport of $P$ with the transport, under the same substitution for the curve `W.fullKernelQuotient Q N`, of $\varphi P$.
--
--   This is the covariance of Vélu's isogeny under isomorphisms of Weierstrass models: reading the quotient isogeny in new coordinates yields the isogeny for the transported kernel. The equality is heterogeneous because the two target curves agree only through [`WeierstrassCurve.fullKernelQuotient_variableChange_vcInvFun`](thm.html#WeierstrassCurve.fullKernelQuotient_variableChange_vcInvFun), which identifies `(C • W).fullKernelQuotient Q' N` with `C • W.fullKernelQuotient Q N`; the result is used in the comparison of moduli points of Vélu quotients on modular curves, including the Atkin–Lehner and $q$-expansion statements that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_heq_fullKernelHom_vcInvFun.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.heq_fullKernelHom_vcInvFun
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (C : VariableChange F)
    (Q : W.toAffine.Point) {N : ℕ} (hQ : addOrderOf Q = N)
    (φ : W.toAffine.Point →+ (W.fullKernelQuotient Q N).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ P : W.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
      (φ P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
    (φ' : (C • W).toAffine.Point →+
      ((C • W).fullKernelQuotient (Point.vcInvFun C W.toAffine Q) N).toAffine.Point)
    (hφ'ker : φ'.ker = AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q))
    (hφ' : ∀ P : (C • W).toAffine.Point, P ∉ AddSubgroup.zmultiples (Point.vcInvFun C W.toAffine Q) →
      (φ' P).coordsOrZero =
        (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1 -
              (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.1),
         P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (N - 1),
            ((P + k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2 -
              (k • Point.vcInvFun C W.toAffine Q).coordsOrZero.2)))
    (P : W.toAffine.Point) :
    HEq (φ' (Point.vcInvFun C W.toAffine P))
      (Point.vcInvFun C (W.fullKernelQuotient Q N).toAffine (φ P)) := by sorry
