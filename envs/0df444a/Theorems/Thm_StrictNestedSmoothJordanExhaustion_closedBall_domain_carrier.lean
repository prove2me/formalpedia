-- Prove2me | Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
-- name    : StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:35.944918+00:00
-- url     : https://prove2.me/theorems/0823db82-6db7-471a-8c2c-fac32d89497e
-- title:
--   Strict Nested Smooth Jordan Exhaustion: closed Ball domain carrier
-- statement:
--   The open carrier of a closed-disk exhaustion stage is its concentric
--   radius-enlarged disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L124-L128
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L124-L128

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

theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).carrier =
      Metric.ball c (smoothApproxRadius n + R) := by sorry

attribute [defeq] StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
