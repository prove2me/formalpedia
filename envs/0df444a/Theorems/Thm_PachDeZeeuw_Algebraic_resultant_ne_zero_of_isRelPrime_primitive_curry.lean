-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_resultant_ne_zero_of_isRelPrime_primitive_curry
-- name    : PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:39:08.84233+00:00
-- url     : https://prove2.me/theorems/5b2094b5-ec72-4da2-84c3-b4ee20c3620d
-- title:
--   Resultant of coprime primitive curries is nonzero
-- statement:
--   Let $p$ and $q$ be bivariate real polynomials whose curried forms are primitive ($h_{pprim} : (\mathrm{Curry0}\,p).\mathrm{IsPrimitive}$, $h_{qprim}$ likewise) and coprime ($h_{rel} : \mathrm{IsRelPrime}\,(\mathrm{Curry0}\,p)\,(\mathrm{Curry0}\,q)$). Then the resultant of the curries is a nonzero coefficient polynomial:
--
--   $${\mathrm{resultant}\,(\mathrm{Curry0}\,p)\,(\mathrm{Curry0}\,q) \neq 0.}$$
--
--   This instantiates the abstract fraction-field criterion at the curried polynomials: primitivity plus coprimality over $\mathrm{XCoeff}$ yields coprimality over $\mathrm{XFrac}$ and hence a nonzero resultant. The nonvanishing resultant is what makes the fiber-counting work --- common zeros can only sit above its finitely many roots.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L520-L528

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry (p q : MvPolynomial (Fin 2) ℝ)
    (hpprim : (Curry0 p).IsPrimitive)
    (hqprim : (Curry0 q).IsPrimitive)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    Polynomial.resultant (Curry0 p) (Curry0 q) ≠ 0 := by sorry
