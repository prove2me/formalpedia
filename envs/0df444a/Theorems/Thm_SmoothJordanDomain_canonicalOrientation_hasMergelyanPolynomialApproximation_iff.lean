-- Prove2me | Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
-- name    : SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:18.496291+00:00
-- url     : https://prove2.me/theorems/28e5f04f-1729-4f6a-9217-9d7dfbe2835e
-- title:
--   Smooth Jordan Domain: canonical Orientation has Mergelyan Polynomial Approximation iff
-- statement:
--   The Smooth Jordan Domain construction uses the canonical Orientation has Mergelyan Polynomial Approximation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L236-L241
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L236-L241

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

theorem SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
    (Omega : SmoothJordanDomain) :
    Omega.canonicalOrientation.HasMergelyanPolynomialApproximation ↔
      Omega.HasMergelyanPolynomialApproximation := by sorry
