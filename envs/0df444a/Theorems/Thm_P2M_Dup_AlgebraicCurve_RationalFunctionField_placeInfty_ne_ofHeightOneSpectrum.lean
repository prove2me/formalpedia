-- Prove2me | Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
-- name    : P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/5ec48eeb-92f6-50ae-bebc-475dbfe352a1
-- title:
--   The place at infinity of K(t) is not a finite place
-- statement:
--   Let $K$ be a field and let $w$ be a height-one prime of the polynomial ring $K[t]$, i.e. an element of the height-one spectrum of the Dedekind domain $\mathrm{Polynomial}\ K$. Two places of the rational function field $\mathrm{RatFunc}\ K$ over $K$ are compared, where a place of an extension $F/K$ is a valuation subring of $F$ containing the image of $K$ under the structure map, different from $F$ itself, and whose ring structure is that of a principal ideal ring. The first is `placeInfty K`, whose valuation subring is that of the infinity valuation `RatFunc.inftyValuation K` of $K(t)$, that is, the subring of rational functions whose numerator degree does not exceed the denominator degree. The second is `Place.ofHeightOneSpectrum w`, whose valuation subring is that of the $w$-adic valuation of $K(t)$ attached to the prime $w$ of $K[t]$, $K(t)$ being the fraction field of $K[t]$. The assertion is that these two places are distinct: $\mathrm{placeInfty}\ K \neq \mathrm{Place.ofHeightOneSpectrum}\ w$ for every such $w$.
--
--   This is the elementary separation, in the classification of the places of the rational function field, between the place at infinity and the finite places indexed by the monic irreducible polynomials; here the places are recorded as valuation subrings of $K(t)$ containing $K$. It is used for the degree computation at infinity and for the reformulation of 'being the place at infinity' as 'not being of the form $v_P$', and thence in the divisor-theoretic bookkeeping for $\mathbb{P}^1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum.lean

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

theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum (K : Type*) [Field K] [DecidableEq (RatFunc K)] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) : placeInfty K ≠ Place.ofHeightOneSpectrum w := by sorry
