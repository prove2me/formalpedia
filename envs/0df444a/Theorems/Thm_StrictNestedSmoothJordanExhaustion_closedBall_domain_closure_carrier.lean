-- Prove2me | Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
-- name    : StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:51.531192+00:00
-- url     : https://prove2.me/theorems/8ff63b3f-cc86-57b9-b9ea-9111cb2a34a5
-- title:
--   Strict Nested Smooth Jordan Exhaustion: closed Ball domain closure carrier
-- statement:
--   The compact control set of a closed-disk exhaustion stage is its
--   concentric radius-enlarged closed disk.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L150-L158
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L150-L158

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

theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    closure
        ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).carrier =
      Metric.closedBall c (smoothApproxRadius n + R) := by sorry
