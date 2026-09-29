-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
-- name    : WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/3190c933-3982-52e5-8936-df1e19a29d91
-- title:
--   Vélu function-field embedding with point map of kernel ⟨ Q⟩
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero, $W$ a Weierstrass curve over $F$ whose associated affine curve is elliptic, $Q$ a point of $W$ and $n$ a natural number with $\mathrm{addOrderOf}\,Q = 2n+1$. Write $S =$ `W.oddOrderSummingSet Q n` for the finite set of coordinate pairs of the multiples $k\cdot Q$, $1 \le k \le n$ (the point at infinity contributing $(0,0)$), and $W' =$ `W.veluQuotient S` for the Weierstrass curve with the same $a_1,a_2,a_3$ and with $a_4' = a_4 - 5\sum_{P\in S} t_P$, $a_6' = a_6 - b_2\sum_{P\in S} t_P - 7\sum_{P\in S} w_P$. Assume $\Delta(W') \ne 0$, that the affine curve of $W'$ is elliptic, and, for each of $W$ and $W'$: a `GenusOnePlaceGate`, i.e. a bijection between points and places of the function field over $F$ with all places of degree one; its `IsCentred` property, that at the place attached to a nonsingular point $(x,y)$ both coordinate-ring classes $X-x$ and $Y-y$ are non-units of the valuation subring; and `AbelTheorem`, that a divisor of degree zero is principal exactly when the sum of its places, transported to points, vanishes. Then there is an $F$-algebra homomorphism $\iota$ from the function field of $W'$ to that of $W$, integral, making the function field of $W$ a finite module over that of $W'$ of rank $2n+1$, such that for every witness of the pushforward norm formula along $\iota$ the resulting homomorphism `pointMapOfPushforward` from the points of $W$ to the points of $W'$ (obtained by conjugating the $\mathrm{Pic}^0$-pushforward along $\iota$ by the genus-one identifications of $\mathrm{Pic}^0$ with the group of points) has kernel the subgroup $\mathbb{Z}\cdot Q$ of multiples of $Q$.
--
--   This is the group-theoretic content of Vélu's construction: the quotient isogeny $W \to W/\langle Q\rangle$ of degree $2n+1$, realised here on function fields and on points via pushforward of degree-zero divisor classes. It is used in the comparison of $j$-invariants of $\ell$-isogenous curves, where the modular polynomial is shown to vanish on the pair $(j(W), j(W'))$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
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
      AlgebraicCurve.finrankAlong F ι = 2 * n + 1
        ∧ ∀ hN : AlgebraicCurve.NormFormulaAlong F ι hfin,
            (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
              = AddSubgroup.zmultiples Q := by sorry
