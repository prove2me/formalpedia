-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_random_input_geometry_ae
-- name    : QEC.Coding.BDL26NativeGeometricJointExecution.native_random_input_geometry_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:58:51.225863+00:00
-- url     : https://prove2.me/theorems/66f4c852-98f5-4cf0-9e9b-c03ee5d94ff2
-- title:
--   BDL26 Native Geometric Joint Execution: native random input geometry ae
-- statement:
--   Fresh product sampling with arbitrary incoming probability law: actual
--   halting and the complete original geometric/density output handoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L1051-L1065
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L1051-L1065

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton

theorem QEC.Coding.BDL26NativeGeometricJointExecution.native_random_input_geometry_ae (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    ∀ᵐ z ∂ν.prod (nativeTableMeasure S n p),
      NativeHalts S n z.1 (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) z.2 ∧
      nativeOutput S n z.1 p z.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n z.1 p ∧
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) z.1 p.lambda (nativeOutput S n z.1 p z.2))
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ center, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) z.1 p.lambda (nativeOutput S n z.1 p z.2)))
        (Metric.closedBall center 1)).card : ℝ) ≤ triangleDensityBound := by sorry
