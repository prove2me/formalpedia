-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
-- name    : WeierstrassCurve.Affine.ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/102db63a-46f1-5a3e-a4bf-eb9199ece59e
-- title:
--   Kernel rigidity for isogenies out of a curve with End=ℤ
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero and let $W$ be an elliptic Weierstrass curve over $F$ whose affine model carries the genus-one place structure (a bijection between $W(F)$ and the places of $F(W)$ over $F$, all of degree $1$), is centred at each point (the classes of $X$ and of $Y-y$ lie in the nonunits of the valuation subring of the place attached to $(x,y)$), and satisfies the Abel theorem (a divisor of degree $0$ is principal exactly when its divisor sum vanishes). Assume moreover: for every isogeny endomorphism datum of $W$, that is every integral, module-finite $F$-algebra embedding $F(W)\hookrightarrow F(W)$, the pushforward norm formula holds (the pushforward of the divisor of a nonzero $f$ has order at each place $v$ equal to $\operatorname{ord}_v$ of the norm of $f$), and the induced endomorphism of $W(F)$ — obtained by transporting through the identification $W(F)\cong\operatorname{Pic}^0$ and pushing divisor classes forward — is $m\cdot\mathrm{id}$ for some $m \in \mathbb{Z}$. Let $V,V'$ be elliptic Weierstrass curves over $F$ likewise equipped with the genus-one place structure and the Abel theorem, and let $\iota \colon F(V) \to F(W)$ and $\iota' \colon F(V') \to F(W)$ be $F$-algebra maps that are integral and module-finite and satisfy the pushforward norm formula. If the kernels of the associated pushforward maps $W(F) \to V(F)$ and $W(F) \to V'(F)$ have the same cardinality and $j(V) = j(V')$, then these two kernels coincide as subgroups of $W(F)$.
--
--   This is the kernel rigidity statement for a curve without complex multiplication: two isogenies out of $W$ whose kernels have the same order and whose targets have equal $j$-invariant differ by an isomorphism of the targets, hence have the same kernel. It underlies the injectivity of $C \mapsto j(W/C)$ on subgroups of a fixed order, and is used in the analysis of the modular polynomial and of the Tate point kernels ([`ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental`](thm.html#ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental) and [`ModularCurve.TatePoint.fullKernelInjAt`](thm.html#ModularCurve.TatePoint.fullKernelInjAt)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WeierstrassCurve.Affine.ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    (hNs : ∀ D : WeierstrassCurve.Affine.IsogenyEndDatum W.toAffine,
      AlgebraicCurve.NormFormulaAlong F D.ι D.hfin)
    (hEnd : ∀ D : WeierstrassCurve.Affine.IsogenyEndDatum W.toAffine,
      ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P = m • P)
    (V V' : WeierstrassCurve F) [V.IsElliptic] [V'.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate V.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem V.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate V'.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem V'.toAffine]
    (ι : V.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι)
    (hN : AlgebraicCurve.NormFormulaAlong F ι hfin)
    (ι' : V'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hι' : ι'.toRingHom.IsIntegral) (hfin' : AlgebraicCurve.FiniteAlong F ι')
    (hN' : AlgebraicCurve.NormFormulaAlong F ι' hfin')
    (hcard : Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
      = Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι' hι' hfin' hN').ker)
    (hj : V.j = V'.j) :
    (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
      = (WeierstrassCurve.Affine.pointMapOfPushforward ι' hι' hfin' hN').ker := by sorry
