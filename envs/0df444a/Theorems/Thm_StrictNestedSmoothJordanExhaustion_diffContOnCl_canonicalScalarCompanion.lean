-- Prove2me | Theorems.Thm_StrictNestedSmoothJordanExhaustion_diffContOnCl_canonicalScalarCompanion
-- name    : StrictNestedSmoothJordanExhaustion.diffContOnCl_canonicalScalarCompanion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:22.923772+00:00
-- url     : https://prove2.me/theorems/9c9ff016-0361-40a1-b810-20a7738d3b65
-- title:
--   Strict Nested Smooth Jordan Exhaustion: diff Cont On Cl canonical Scalar Companion
-- statement:
--   Every canonical closed scalar companion on a bundled smooth stage has the
--   regularity required by complex polynomial approximation: it is continuous on
--   the compact closure and complex differentiable in the carrier.  Canonical
--   orientation supplies winding one, while compactness supplies boundedness.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L187-L216
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L187-L216

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

theorem StrictNestedSmoothJordanExhaustion.diffContOnCl_canonicalScalarCompanion
    {K : Set ℂ} (Omega : StrictNestedSmoothJordanExhaustion K)
    (p : Polynomial ℂ) (n : ℕ) :
    DiffContOnCl ℂ
      (crouzeixPolynomialScalarCompanionClosedExtension
        (Omega.domain n).canonicalOrientation p)
      (Omega.domain n).canonicalOrientation.carrier := by sorry
