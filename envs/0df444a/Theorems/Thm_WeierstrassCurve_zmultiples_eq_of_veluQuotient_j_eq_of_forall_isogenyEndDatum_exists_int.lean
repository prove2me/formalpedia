-- Prove2me | Theorems.Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int
-- name    : WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/012791e6-9417-5e9d-b060-7ab6c0060cd8
-- title:
--   Equal j of Vélu quotients forces equal cyclic subgroups
-- statement:
--   Let $\mathbb{K}=\mathrm{HahnSeries}\,\mathbb{Q}\,\overline{\mathbb{Q}}$ be the field of Hahn series with rational exponents and coefficients in an algebraic closure of $\mathbb{Q}$, assumed algebraically closed of characteristic $0$, and let $W$ be an elliptic Weierstrass curve over $\mathbb{K}$. Assume for its affine model: a `GenusOnePlaceGate`, i.e. a bijection between $W$'s affine point group and the places of its function field over $\mathbb{K}$, all of degree $1$; that this gate is centred, i.e. for each nonsingular $(x,y)$ the classes of the coordinate functions $X$ and $Y-y$ lie in the nonunits of the valuation subring at the corresponding place; and `AbelTheorem`, i.e. a degree-zero divisor is principal exactly when its divisor sum vanishes. Assume further that for every isogeny endomorphism datum $D$ of $W$ (an integral $\mathbb{K}$-algebra endomorphism $\iota$ of the function field along which the field is module-finite over itself) the pushforward norm formula holds along $D.\iota$, and that the induced endomorphism $D.\mathrm{pointEnd}$ of the point group is multiplication by some integer $m$. Let $n\in\mathbb{N}$ and let $Q,Q'$ both have additive order $2n+1$. Suppose the Vélu quotient curves formed from the summing sets $\{(k\cdot Q)\text{-coordinates}:1\le k\le n\}$, resp. for $Q'$, have nonzero discriminant, hence are elliptic, and have equal $j$-invariants. Then the subgroups of integer multiples of $Q$ and of $Q'$ coincide.
--
--   This is the injectivity-on-cyclic-subgroups statement for $j$ of Vélu quotients for a curve whose endomorphisms are all integer multiples (Silverman, AEC III.4.12 in the form $\operatorname{Hom}(E,E')\cong\mathbb{Z}$): distinct cyclic subgroups of the same odd order give quotients with distinct $j$-invariants. It feeds the companion statement [`WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental`](thm.html#WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental), where the hypotheses on endomorphisms are replaced by transcendence of the parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

theorem WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))] [CharZero (HahnSeries ℚ (AlgebraicClosure ℚ))]
    [IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong (HahnSeries ℚ (AlgebraicClosure ℚ)) D.ι D.hfin)
    (hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P = m • P)
    (n : ℕ) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) (hQ' : addOrderOf Q' = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q' n)).Δ ≠ 0)
    (hj : haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.veluQuotient (W.oddOrderSummingSet Q' n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j = (W.veluQuotient (W.oddOrderSummingSet Q' n)).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' := by sorry
