-- Prove2me | Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
-- name    : StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:21.509497+00:00
-- url     : https://prove2.me/theorems/b9058196-5c1f-5c23-a53d-d5d81a77e72c
-- title:
--   Strict Nested Smooth Jordan Exhaustion: closed Ball domain boundary Param deriv
-- statement:
--   The derivative of a closed-disk exhaustion contour is the usual tangent
--   to its standard circle parametrization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L140-L146
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L140-L146

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

theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (t : ℝ) :
    deriv
        ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).boundaryParam t =
      circleMap 0 (smoothApproxRadius n + R) t * I := by sorry
