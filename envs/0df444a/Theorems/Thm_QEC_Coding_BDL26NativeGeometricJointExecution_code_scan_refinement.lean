-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_code_scan_refinement
-- name    : QEC.Coding.BDL26NativeGeometricJointExecution.code_scan_refinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:56:26.486135+00:00
-- url     : https://prove2.me/theorems/f028dd18-2538-4080-acf1-4d24289a0e56
-- title:
--   BDL26 Native Geometric Joint Execution: code scan refinement
-- statement:
--   Full paid-pair conjugacy, including rejected candidates and native sorting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L148-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L148-L157

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

theorem QEC.Coding.BDL26NativeGeometricJointExecution.code_scan_refinement (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (R : SR.Rows (SR.Index S n)) :
    codeScanQ S n J r lambda K R =
      (eraseChoice S n J r (scanQ S n J hr lambda K R).1,
        (scanQ S n J hr lambda K R).2) := by sorry
