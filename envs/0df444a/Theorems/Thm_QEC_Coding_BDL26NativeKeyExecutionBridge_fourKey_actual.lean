-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_fourKey_actual
-- name    : QEC.Coding.BDL26NativeKeyExecutionBridge.fourKey_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:41:04.774891+00:00
-- url     : https://prove2.me/theorems/56260dd5-4572-49e9-8853-f7b5b2d9bc83
-- title:
--   BDL26 Native Key Execution Bridge: four Key actual
-- statement:
--   The BDL26 Native Key Execution Bridge construction uses the four Key actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L281-L314
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L281-L314

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective

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

theorem QEC.Coding.BDL26NativeKeyExecutionBridge.fourKey_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (row : LiveRow S n J r) :
    (fourKeyQ row.val.val.1).1 =
      scanKey (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r row) := by sorry
