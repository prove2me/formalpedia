-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecutionCost_native_stopping_original
-- name    : QEC.Coding.BDL26NativeGeometricExecutionCost.native_stopping_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:08:52.984553+00:00
-- url     : https://prove2.me/theorems/f684752d-b834-43f2-b769-6bfd196692fe
-- title:
--   BDL26 Native Geometric Execution Cost: native stopping original
-- statement:
--   The emitter materializes every original vertex value in native address
--   order; the generated trace and every original counter are retained as well.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L789-L825
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L789-L825

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecutionCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeGeometricExecutionCost.native_stopping_original (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : OriginalTable S n)
    (h : NativeHalts S n J hr lambda K (SR.encodeSamples S n T)) :
    let m := nativeHaltTime S n J hr lambda K (SR.encodeSamples S n T)
    let stopped := (stopQ S n J hr lambda K (SR.encodeSamples S n T) (m+1)).value
    stopped.emitted=some ((SR.indices (SR.count S n)).map (fun a =>
      (a,returned S n J hr lambda K (SR.encodeSamples S n T) (SR.decode S n a)))) ∧
    stopped.state.trace.map (Option.map (event S n J r))=originalTrace S n J r lambda K T m ∧
    ∀ v : Vertex (Presentation S n),
      (SR.readQ ((SR.decode S n).symm v) stopped.state.rows).value=
        (counters (X := fun _ : Vertex (Presentation S n) => Space)
            (U S n J r) (B S n J r lambda K) T m v,
          returned S n J hr lambda K (SR.encodeSamples S n T) v) := by sorry
