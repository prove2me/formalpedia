-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_isRelPrime_fraction_map_of_isPrimitive
-- name    : PachDeZeeuw.Algebraic.isRelPrime_fraction_map_of_isPrimitive
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:38:23.544507+00:00
-- url     : https://prove2.me/theorems/38ca69e9-47df-4617-ad78-0a6d51c4d237
-- title:
--   Coprimality survives mapping primitive polynomials to the fraction field
-- statement:
--   Let $P$ and $Q$ be primitive univariate polynomials over the coefficient ring $\mathrm{XCoeff}$ ($P.\mathrm{IsPrimitive}$, $Q.\mathrm{IsPrimitive}$) that are relatively prime ($\mathrm{IsRelPrime}\,P\,Q$). Then their images under the fraction-field map remain relatively prime:
--
--   $$\mathrm{IsRelPrime}(P.\mathrm{map}(\mathrm{algebraMap}\,\mathrm{XCoeff}\,\mathrm{XFrac}),\, Q.\mathrm{map}(\mathrm{algebraMap}\,\mathrm{XCoeff}\,\mathrm{XFrac})).$$
--
--   This Gauss-lemma-style transport moves coprimality from the UFD $\mathrm{XCoeff}$ to its fraction field $\mathrm{XFrac}$, where a common factor would force the resultant to vanish; contrapositively it yields resultant nonvanishing for primitive coprime currys.
-- source:
--   Standard algebra used in proving Bézout's inequality, Theorem 2.1 of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), which cites Gibson, Elementary Geometry of Algebraic Curves, Lemma 14.4; this lemma is not stated in the paper; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L382-L507

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.isRelPrime_fraction_map_of_isPrimitive (P Q : Polynomial XCoeff)
    (hPprim : P.IsPrimitive)
    (hQprim : Q.IsPrimitive)
    (hrel : IsRelPrime P Q) :
    IsRelPrime (P.map (algebraMap XCoeff XFrac))
               (Q.map (algebraMap XCoeff XFrac)) := by sorry
