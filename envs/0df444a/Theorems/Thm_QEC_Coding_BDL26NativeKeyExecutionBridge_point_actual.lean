-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_point_actual
-- name    : QEC.Coding.BDL26NativeKeyExecutionBridge.point_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:34:03.811846+00:00
-- url     : https://prove2.me/theorems/226620ec-48ef-4f80-a1b0-a9d05e6dd1c3
-- title:
--   BDL26 Native Key Execution Bridge: point actual
-- statement:
--   The BDL26 Native Key Execution Bridge construction uses the point actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L466-L472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L466-L472

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeKeyExecutionBridge
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeKeyExecutionBridge.point_actual (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (a : SR.Index S n) :
    (pointQ S n lambda (incomingQ S n J).value R a).1 =
      lambda • ((1/2 : ℝ) • J (SR.decode S n a)) +
        originalPoints S n R (SR.decode S n a) := by sorry
