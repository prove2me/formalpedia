-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq
-- name    : P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/10c978df-0cda-523d-ad8c-b753a669abe3
-- title:
--   Equivalence with v's adic valuation from equal valuation rings
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project's structure `Place K F`: a valuation subring $\mathcal{O}_v \subseteq F$ (recorded as `v.toValuationSubring`) which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Attached to $v$ is the height-one prime of $\mathcal{O}_v$ given by its maximal ideal, and `v.adicValuation` is the associated $\mathbb{Z}^{m0}$-valued valuation on $F$, i.e. the valuation of $F$ determined by that height-one prime, with values in $\mathbb{Z}^{m0} = \mathbb{Z}^{\mathrm{multiplicative}}$ adjoined zero. The theorem asserts: for any linearly ordered commutative group with zero $\Gamma$ and any valuation $w : F \to \Gamma$ whose valuation subring $\{x \in F : w(x) \le 1\}$ coincides with $\mathcal{O}_v$, the valuation $w$ is equivalent to `v.adicValuation` in Mathlib's sense (`Valuation.IsEquiv`), that is, the two induce the same order relation on $F$, hence differ only by a rescaling of value groups.
--
--   This is the standard fact that a valuation on a field is determined up to equivalence by its valuation ring, specialised to the normalised (discrete, $\mathbb{Z}$-valued) valuation attached to a place of $F/K$. It is used to identify arbitrary valuations with the normalised one, feeding into the computation of the order function of a place and into the degree-one criterion for places of a rational function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation := by sorry
