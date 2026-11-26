-- Prove2me | Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
-- name    : StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:50:56.516437+00:00
-- url     : https://prove2.me/theorems/6a7e45ea-7f52-5674-a974-8e5a8c33ee41
-- title:
--   Strict Nested Smooth Jordan Exhaustion: closed Ball domain boundary Param outward Normal
-- statement:
--   Multiplication of the disk-contour tangent by `-I` yields the radial
--   outward normal.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L174-L181
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L174-L181

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

theorem StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (t : ℝ) :
    -I * deriv
        ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).boundaryParam t =
      circleMap 0 (smoothApproxRadius n + R) t := by sorry
