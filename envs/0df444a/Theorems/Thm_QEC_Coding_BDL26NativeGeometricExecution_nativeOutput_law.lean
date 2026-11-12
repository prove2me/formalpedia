-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_nativeOutput_law
-- name    : QEC.Coding.BDL26NativeGeometricExecution.nativeOutput_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:07:22.862571+00:00
-- url     : https://prove2.me/theorems/6fe6c4f6-4723-4afb-9a1f-b44c8ac75564
-- title:
--   BDL26 Native Geometric Execution: native Output law
-- statement:
--   Full native output pushforward; this is not a claim of product independence
--   of the adaptively selected output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L461-L470
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L461-L470

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective

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

theorem QEC.Coding.BDL26NativeGeometricExecution.nativeOutput_law (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L) :
    (nativeTableMeasure S n p).map (nativeOutput S n J p) =
      (tableMeasure (Presentation S n) p).map
        (result (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J p) := by sorry
