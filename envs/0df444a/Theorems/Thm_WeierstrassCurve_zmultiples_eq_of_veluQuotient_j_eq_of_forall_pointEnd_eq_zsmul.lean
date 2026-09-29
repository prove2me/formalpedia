-- Prove2me | Theorems.Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul
-- name    : WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/0e7a973d-770c-5911-9142-996e882938dd
-- title:
--   Equal j of Vélu quotients forces equal cyclic subgroups
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero with decidable equality, and let $W$ be a Weierstrass curve over $F$ which is elliptic. Assume the affine curve $W.\mathrm{toAffine}$ carries the three structures used throughout: a `GenusOnePlaceGate`, i.e. a bijection between the points of $W$ and the places of its function field over $F$ together with the assertion that every such place has degree $1$; the centredness property `GenusOnePlaceGate.IsCentred`, i.e. for each nonsingular affine point $(x,y)$ the classes of the coordinate functions $X$ and $Y-y$ lie in the nonunits of the valuation subring of the associated place; and `AbelTheorem`, i.e. a divisor of degree $0$ is principal exactly when its divisor sum in the group of points vanishes. Assume further: `hNs`, that for every isogeny endomorphism datum $D$ on $W.\mathrm{toAffine}$ — an integral $F$-algebra endomorphism $\iota$ of the function field making it a finite module over itself along $\iota$ — the pushforward norm formula holds along $\iota$, namely that for every nonzero $f$ and every divisor given by the orders of $f$, the pushforward of that divisor takes at each place $v$ the value $v(\mathrm{N}(f))$; and `hEnd`, that for every such datum $D$ there is an integer $m$ with $D.\mathrm{pointEnd}\,P = m\cdot P$ for all points $P$, i.e. the endomorphisms arising from these data are exactly multiplications by integers. Let $n$ be a natural number and $Q,Q'$ points of $W$ both of additive order $2n+1$. Suppose the Vélu curves $W.\mathrm{veluQuotient}$ formed from the summing sets $\{(k\cdot Q)\ \text{coordinates} : 1\le k\le n\}$ and likewise for $Q'$ — the Weierstrass curves with unchanged $a_1,a_2,a_3$ and with $a_4$ and $a_6$ modified by the Vélu sums — have nonzero discriminants, hence are elliptic, and have equal $j$-invariants. Then the subgroups of integer multiples of $Q$ and of $Q'$ coincide.
--
--   This is the statement that an elliptic curve whose endomorphisms of the point group coming from isogeny data are all multiplications by integers (no complex multiplication) has the property that distinct cyclic subgroups of the same odd order have Vélu quotients with distinct $j$-invariants; classically it is the rigidity step behind Silverman, Arithmetic of Elliptic Curves III.4.11–4.12. It is used in establishing separability of the modular polynomial specialised at a point, via [`ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed`](thm.html#ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

theorem WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_pointEnd_eq_zsmul
    {F : Type u} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong F D.ι D.hfin)
    (hEnd : ∀ D : IsogenyEndDatum W.toAffine, ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P = m • P)
    (n : ℕ) (Q Q' : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) (hQ' : addOrderOf Q' = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q' n)).Δ ≠ 0)
    (hj : haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
      haveI : (W.veluQuotient (W.oddOrderSummingSet Q' n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j = (W.veluQuotient (W.oddOrderSummingSet Q' n)).j) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples Q' := by sorry
