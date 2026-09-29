-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub
-- name    : WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd_apply_eq_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/2a48382c-2930-5c17-be93-7b0083958996
-- title:
--   Point endomorphism of an isogeny datum equals h(P)-h(O)
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $0$ and let $W$ be an affine Weierstrass curve over $F$ which is elliptic, equipped with two structures: `GenusOnePlaceGate W`, consisting of a bijection `pointEquivPlace` between the group $W(F)$ of points `W.Point` and the set of places of the function field `W.FunctionField` over $F$ (a place being a proper valuation subring containing the image of $F$ and having principal ideals) together with the assertion that every such place has degree $1$; and `AbelTheorem W`, the assertion that a divisor of degree $0$ on `W.FunctionField` is principal exactly when its `divisorSum`, the image of its point support under the dictionary, vanishes. Let $D$ be an `IsogenyEndDatum` for $W$, i.e. an $F$-algebra endomorphism $\iota = D.\iota$ of `W.FunctionField` whose underlying ring map is integral and which makes `W.FunctionField` a finite module over itself, and assume `hN`, the push-forward norm formula along $\iota$: for every nonzero $f$ and every divisor equal to $\operatorname{div}(f)$ upstairs, the push-forward takes at each place $v$ downstairs the value $v(\mathrm{N}(f))$. Then for every point $P$ the additive endomorphism `D.pointEnd hN` of `W.Point` satisfies $$D.\text{pointEnd}\,hN\,(P) = \iota^{*}(v_P) - \iota^{*}(v_O),$$ where $v_Q$ denotes `placeOfPoint Q`, $\iota^{*}$ is `Place.restrictAlong D.ι D.hι` (the valuation subring pulled back along $\iota$), and both places are carried back to points by the inverse of `pointEquivPlace`; here $O$ is the zero point.
--
--   This is the rigidity statement in the conditional place-theoretic set-up: the group endomorphism of $W(F)$ obtained by transporting push-forward of degree-zero divisors along $\iota$ through the Abel–Jacobi dictionary is the geometric self-map $h$ determined by $\iota$ on places, corrected by subtracting $h(O)$, so that $h$ is a translation composed with an isogeny. It is used by [`WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_add`](thm.html#WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_add), which passes between morphism-level identities for $\iota$ and additive identities for `pointEnd`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.lean

import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd_apply_eq_sub
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) (P : W.Point) :
    D.pointEnd hN P
      = (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι)
        - (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) := by sorry
