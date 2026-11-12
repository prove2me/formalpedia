-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_encoded_decoded
-- name    : QEC.Coding.BDL26NativeGeometricExecution.encoded_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:42:01.853562+00:00
-- url     : https://prove2.me/theorems/21e8bb01-1e91-4a6c-8c40-d44f2fb562b0
-- title:
--   BDL26 Native Geometric Execution: encoded decoded
-- statement:
--   The BDL26 Native Geometric Execution construction uses the encoded decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L358-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L358-L360

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeGeometricExecution.encoded_decoded (S : OddScale) (n : ℕ) (T : NativeTable S n) :
    SR.encodeSamples S n (decodedTable S n T) = T := by sorry
