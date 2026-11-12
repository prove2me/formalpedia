-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_triangle_actual
-- name    : QEC.Coding.BDL26NativeKeyExecutionBridge.triangle_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:47:27.909198+00:00
-- url     : https://prove2.me/theorems/3e5c30ff-4acb-43f9-ba07-815c51d77341
-- title:
--   BDL26 Native Key Execution Bridge: triangle actual
-- statement:
--   The BDL26 Native Key Execution Bridge construction uses the triangle actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L488-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L488-L516

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

theorem QEC.Coding.BDL26NativeKeyExecutionBridge.triangle_actual (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    (lambda : ℝ) (R : SR.Rows (SR.Index S n)) (a : Triangle (Presentation S n))
    (center : Space) :
    (triangleCodeQ S n J lambda R (MD.triangleCode S n a) center).1 = true ↔
      (fun i => originalPoints S n R (triangleVertex (Presentation S n) a i)) ∈
      triangleHit (fun i => lambda • ((1/2 : ℝ) • J (triangleVertex (Presentation S n) a i)))
        center 2 := by sorry
