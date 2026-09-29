-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one
-- name    : P2M.Dup.AlgebraicCurve.Place.ord_eq_zero_iff_adicValuation_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/543bb235-c2f6-5043-93bd-8f039c096e0f
-- title:
--   Order zero at a place iff adic valuation one
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is, a valuation subring $\mathcal{O}_v \subseteq F$ containing the image of $K$ under the structure map, distinct from all of $F$, and whose underlying ring is a principal ideal ring (hence a discrete valuation ring). Attached to $v$ is its height-one prime, the maximal ideal of $\mathcal{O}_v$, and the induced valuation $v.\mathrm{adicValuation} : F \to \mathbb{Z}^{m0}$, the valuation on the fraction field $F$ associated with that height-one prime, with values in $\mathbb{Z}$ written multiplicatively and adjoined zero; the order function is $v.\mathrm{ord}(f) = -\log\big(v.\mathrm{adicValuation}(f)\big) \in \mathbb{Z}$, where $\log$ is the inverse of the multiplicative-to-additive identification, sending the adjoined zero to $0$. The theorem asserts that for every $f \in F$ with $f \neq 0$ one has $v.\mathrm{ord}(f) = 0$ if and only if $v.\mathrm{adicValuation}(f) = 1$. The hypothesis $f \neq 0$ is what rules out the degenerate direction, since the adic valuation of $0$ is the adjoined zero element, whose logarithm is also $0$.
--
--   This is the elementary compatibility between the additive order of vanishing at a place and the multiplicatively written adic valuation: a nonzero function is a unit at $v$ exactly when its order is zero. It is used in the divisor-theoretic part of the development, for instance in the norm formula for pushforwards of divisors and in recognising unramified places from divisibility properties of orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem P2M.Dup.AlgebraicCurve.Place.ord_eq_zero_iff_adicValuation_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by sorry
