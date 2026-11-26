-- Prove2me | Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
-- name    : StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:46.448923+00:00
-- url     : https://prove2.me/theorems/5cfeeafc-1643-4286-b516-ebc3f5ced395
-- title:
--   Strict Nested Smooth Jordan Exhaustion: closed Ball domain boundary Param
-- statement:
--   The boundary trace of a closed-disk exhaustion stage is its standard
--   circle parametrization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L132-L136
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L132-L136

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

theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).boundaryParam =
      circleMap c (smoothApproxRadius n + R) := by sorry

attribute [defeq] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
