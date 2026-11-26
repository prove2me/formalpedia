-- Prove2me | Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
-- name    : SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:56.47318+00:00
-- url     : https://prove2.me/theorems/2032bdfd-4766-5b60-89f5-6003c358d89a
-- title:
--   Smooth Jordan Domain: reverse Orientation has Mergelyan Polynomial Approximation iff
-- statement:
--   The Smooth Jordan Domain construction uses the reverse Orientation has Mergelyan Polynomial Approximation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L230-L234
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L230-L234

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real

theorem SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
    (Omega : SmoothJordanDomain) :
    Omega.reverseOrientation.HasMergelyanPolynomialApproximation ↔
      Omega.HasMergelyanPolynomialApproximation := by sorry
