-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_resultant_ne_zero_of_fraction_coprime
-- name    : PachDeZeeuw.Algebraic.resultant_ne_zero_of_fraction_coprime
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:30.56966+00:00
-- url     : https://prove2.me/theorems/3dcf1c95-78ca-4a09-bc22-e6e20d43e235
-- title:
--   Resultant nonzero for polynomials coprime over the fraction field
-- statement:
--   Let $P$ and $Q$ be univariate polynomials over the coefficient ring $\mathrm{XCoeff} = \mathrm{MvPolynomial}\,(\mathrm{Fin}\,1)\,\mathbb{R}$, and assume coprimality after base change to its fraction field, $h_{cop} : \mathrm{IsCoprime}\,(P.\mathrm{map}\,\mathrm{algebraMap})\,(Q.\mathrm{map}\,\mathrm{algebraMap})$ over $\mathrm{XFrac} = \mathrm{FractionRing}\,\mathrm{XCoeff}$. Then their resultant is nonzero:
--
--   $${\mathrm{resultant}\,P\,Q \neq 0.}$$
--
--   This is the abstract resultant criterion: coprimality over a field (here the fraction field of the UFD $\mathrm{XCoeff}$) forces a nonzero resultant, since the Sylvester determinant detects a common factor. It is the bridge from the fraction-field coprimality obtained via primitivity lemmas to the concrete nonvanishing of the resultant polynomial whose roots are then counted.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L356-L380

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.resultant_ne_zero_of_fraction_coprime (P Q : Polynomial XCoeff)
    (hcop : IsCoprime (P.map (algebraMap XCoeff XFrac))
                       (Q.map (algebraMap XCoeff XFrac))) :
    Polynomial.resultant P Q ≠ 0 := by sorry
