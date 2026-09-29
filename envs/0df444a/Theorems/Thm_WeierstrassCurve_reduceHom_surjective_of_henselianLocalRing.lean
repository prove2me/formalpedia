-- Prove2me | Theorems.Thm_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing
-- name    : WeierstrassCurve.reduceHom_surjective_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/036a12b7-cb35-5eab-90bd-b66d8a3e0a9b
-- title:
--   Surjectivity of reduction for good reduction over a Henselian valuation ring
-- statement:
--   Let $L$ be a field and let $A \subseteq L$ be a valuation subring which, as a local ring, is Henselian; write $\mathrm{residue}_A \colon A \to \kappa$ for the quotient map onto its residue field $\kappa$. Let $W$ be a Weierstrass curve with coefficients in $A$, and assume that the reduced Weierstrass curve $W \bmod \mathfrak m$ over $\kappa$, obtained by applying $\mathrm{residue}_A$ to the coefficients $a_1, a_2, a_3, a_4, a_6$, has nonzero discriminant $\Delta$. The assertion is that the additive map [`WeierstrassCurve.reduceHom`](def/WeierstrassCurve_ReduceHom.html#L481) associated with this hypothesis is surjective as a function. Its source is the group of affine points (in the sense of the Mathlib `Affine.Point` construction, so nonsingular points together with the point at infinity) of $W$ base changed along the inclusion $A \hookrightarrow L$, its target is the group of affine points of the reduced curve over $\kappa$, and it is induced by the map sending the point at infinity to the point at infinity, sending an affine point $(x,y)$ with $x \in A$ to the point with coordinates $\mathrm{residue}_A(x)$ and $\mathrm{residue}_A(y)$ (the second coordinate lying in $A$ automatically, and the resulting point being nonsingular by the discriminant hypothesis), and sending an affine point with $x \notin A$ to the point at infinity.
--
--   This is the surjectivity half of the standard description of reduction of points on a Weierstrass curve with good reduction over a Henselian (in particular complete) valuation ring, as in Silverman VII.2.1: every point of the reduced curve over the residue field lifts to a point with coordinates in $A$, by Hensel's lemma applied to the Weierstrass polynomial in whichever variable its partial derivative is nonzero at the given residue point. It is used in the construction, for an algebraically closed residue field, of a valuation subring together with an identification of its residue field compatible with the reduction map on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.reduceHom_surjective_of_henselianLocalRing
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [HenselianLocalRing A]
    [DecidableEq (IsLocalRing.ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (IsLocalRing.residue A)).Δ ≠ 0) :
    Function.Surjective (WeierstrassCurve.reduceHom hΔ) := by sorry
