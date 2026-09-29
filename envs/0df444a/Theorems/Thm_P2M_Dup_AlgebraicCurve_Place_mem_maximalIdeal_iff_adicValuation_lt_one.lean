-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one
-- name    : P2M.Dup.AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/a8e08be7-d4e9-541b-96b8-7d67bcaa2dc7
-- title:
--   Maximal ideal of a place: v-valuation <1
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project's structure `Place K F`: a valuation subring $\mathcal{O}_v \subseteq F$ (written `v.toValuationSubring`) which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Since $\mathcal{O}_v$ is then a discrete valuation ring, its maximal ideal determines a point `v.heightOneSpectrum` of the height-one spectrum of $\mathcal{O}_v$, and `v.adicValuation` denotes the associated $\mathbb{Z}^{m0}$-valued valuation on the fraction field $F$. The assertion is that for an element $a$ of the subring $\mathcal{O}_v$, the element $a$ lies in the maximal ideal of the local ring $\mathcal{O}_v$ if and only if the value of `v.adicValuation` at the image of $a$ in $F$ is strictly less than $1$.
--
--   This is the standard identification of the maximal ideal of the valuation ring of a place with the set of elements of positive valuation, in the form needed to pass between ideal-theoretic and valuation-theoretic descriptions of a place. It is used in the development of places, divisors and the divisor class group of a function field, for instance in the computation of places of the rational function field and in statements about evaluation at a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := by sorry
