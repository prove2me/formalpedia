-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_not_both_specializations_zero_of_isRelPrime
-- name    : PachDeZeeuw.Algebraic.not_both_specializations_zero_of_isRelPrime
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:33.881548+00:00
-- url     : https://prove2.me/theorems/f529319a-ed52-427a-bcac-e85a50811829
-- title:
--   Coprime primitive curries never specialize both to zero
-- statement:
--   Let $p$ and $q$ be bivariate real polynomials, let $x : \mathbb{R}$ be a coefficient coordinate, and assume the curried forms are relatively prime, $h_{rel} : \mathrm{IsRelPrime}\,(\mathrm{Curry0}\,p)\,(\mathrm{Curry0}\,q)$. The statement also carries primitivity hypotheses on the curries (binders `_hpprim` $: (\mathrm{Curry0}\,p).\mathrm{IsPrimitive}$ and `_hqprim` $: (\mathrm{Curry0}\,q).\mathrm{IsPrimitive}$); they are present in the statement but not used by the proof. Then the two specialized univariate polynomials at $x$ do not both vanish:
--
--   $${\mathrm{Specialized0}\,x\,p \neq 0 \lor \mathrm{Specialized0}\,x\,q \neq 0.}$$
--
--   The proof shows that if both specializations vanished, the line factor $\mathrm{CoeffLineFactor}\,x$ would divide both $p$ and $q$, hence its curry would divide both curries and would be a unit by $h_{rel}$; but that factor has a nonzero coefficient of positive degree, so it is not a unit. In the resultant/fiber-counting argument this guarantees that, over each coefficient value $x$, the common zeros are roots of a nonzero univariate polynomial.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L702-L765

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.not_both_specializations_zero_of_isRelPrime (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (_hpprim : (Curry0 p).IsPrimitive)
    (_hqprim : (Curry0 q).IsPrimitive)
    (hrel : IsRelPrime (Curry0 p) (Curry0 q)) :
    Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0 := by sorry
