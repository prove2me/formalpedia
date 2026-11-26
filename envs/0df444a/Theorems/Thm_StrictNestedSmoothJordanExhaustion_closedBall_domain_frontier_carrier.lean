-- Prove2me | Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
-- name    : StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:29.271896+00:00
-- url     : https://prove2.me/theorems/d5b7c3b9-38ae-4560-8725-ab2509164df7
-- title:
--   Strict Nested Smooth Jordan Exhaustion: closed Ball domain frontier carrier
-- statement:
--   The frontier of a closed-disk exhaustion stage is its concentric metric
--   sphere.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L162-L170
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L162-L170

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

theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    frontier
        ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).carrier =
      Metric.sphere c (smoothApproxRadius n + R) := by sorry
