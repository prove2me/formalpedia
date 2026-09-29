-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
-- name    : P2M.Dup.AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/c0f27816-d641-5c01-9328-7eb6d67b8805
-- title:
--   Places of K(t): the finite places and ∞
-- statement:
--   Let $K$ be a field and consider the rational function field $\mathrm{RatFunc}\,K$ as a $K$-algebra. A `Place K (RatFunc K)` is a valuation subring of $\mathrm{RatFunc}\,K$ which contains the image of $K$ under the structure map, is not the whole field, and is a principal ideal ring. The assertion is that every such place $v$ satisfies one of two alternatives: either there is a height-one prime $w$ of the polynomial ring $K[X]$ with $v =$ `Place.ofHeightOneSpectrum w`, that is, $v$ is the valuation subring of the $w$-adic valuation of $K[X]$ extended to its fraction field $\mathrm{RatFunc}\,K$; or $v =$ `placeInfty K`, the place whose valuation subring is that of `RatFunc.inftyValuation K`, the valuation attached to the degree function at infinity. The disjunction is stated as an inclusive `Or`, with the first alternative an existential over height-one primes; no hypothesis beyond $v$ being a place is imposed.
--
--   This is Ostrowski's classification of the places of a rational function field over $K$ (equivalently, of the valuations of $K(t)$ trivial on $K$): the points of $\mathbb{P}^1$, namely the closed points of the affine line together with the point at infinity. It is the basic enumeration underlying the divisor-theoretic and local-analytic work with places of $K(t)$ in the development, and is cited by results on orders at places and on integrality of polynomials away from infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty.lean

import Mathlib
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : (∃ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by sorry
