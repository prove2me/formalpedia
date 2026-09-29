-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples_of_oddOrder
-- name    : WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples_of_oddOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/44f8253f-ac3c-5c57-a620-3d9729e4c128
-- title:
--   Vélu pushforward point map has kernel ℤQ
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $0$, let $W$ be a Weierstrass curve over $F$ whose associated affine curve is elliptic, let $Q$ be a point of $W.\mathrm{toAffine}.\mathrm{Point}$ and $n$ a natural number with $\mathrm{addOrderOf}\,Q = 2n+1$. Write $W'$ for `W.veluQuotient (W.oddOrderSummingSet Q n)`, the Weierstrass curve with the same $a_1,a_2,a_3$ and with $a_4$ and $a_6$ modified by Vélu's sums over the finite set of coordinate pairs of $Q, 2Q, \dots, nQ$; assume its discriminant $\Delta$ is nonzero and that its affine curve is elliptic. Assume further, for each of $W.\mathrm{toAffine}$ and $W'.\mathrm{toAffine}$: a `GenusOnePlaceGate`, i.e. a bijection between the point group and the places of the function field over $F$ together with the statement that every such place has degree $1$; that this gate is centred, i.e. for every nonsingular affine point $(x,y)$ the classes of $X-x$ and $Y-y$ in the function field are nonunits in the valuation subring of the corresponding place; and `AbelTheorem`, i.e. a degree-zero divisor is principal exactly when its divisor sum vanishes. Then there exist an $F$-algebra homomorphism $\iota$ from the function field of $W'.\mathrm{toAffine}$ to that of $W.\mathrm{toAffine}$, a proof that $\iota$ is integral as a ring homomorphism, and a proof that the target is a finite module over the source via $\iota$, such that for every witness of the pushforward norm formula along $\iota$ (the pushforward of the divisor of any nonzero $f$ has order $v(\mathrm{N}f)$ at each place $v$) the kernel of the induced additive map `pointMapOfPushforward` from $W.\mathrm{toAffine}.\mathrm{Point}$ to $W'.\mathrm{toAffine}.\mathrm{Point}$, obtained by transporting the $\mathrm{Pic}^0$-pushforward along $\iota$ through the genus-one identifications of points with $\mathrm{Pic}^0$, is exactly the subgroup of integer multiples of $Q$.
--
--   This is the kernel half of Vélu's construction of the quotient isogeny $W \to W/\langle Q\rangle$ for a point $Q$ of odd order, realised on function fields and transported to point groups through $\mathrm{Pic}^0$. It feeds the construction of isogenies with prescribed full kernel, via [`WeierstrassCurve.exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples`](thm.html#WeierstrassCurve.exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples_of_oddOrder.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples_of_oddOrder
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
    {Q : W.toAffine.Point} {n : ℕ} (hord : addOrderOf Q = 2 * n + 1)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      ∀ hN : AlgebraicCurve.NormFormulaAlong F ι hfin,
        (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
          = AddSubgroup.zmultiples Q := by sorry
