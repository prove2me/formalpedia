-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_center_actual
-- name    : QEC.Coding.BDL26NativeKeyExecutionBridge.center_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:48:51.973095+00:00
-- url     : https://prove2.me/theorems/a8afbecb-5db7-485a-8931-89eeeb04c04f
-- title:
--   BDL26 Native Key Execution Bridge: center actual
-- statement:
--   The BDL26 Native Key Execution Bridge construction uses the center actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L617-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L617-L631

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

theorem QEC.Coding.BDL26NativeKeyExecutionBridge.center_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r lambda : ℝ) (K : ℕ)
    (row : LiveRow S n J r) (g : Grid K) :
    (centerQ S n J lambda K row.val.val.1 g).1 =
      keyCenter (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r lambda K (event S n J r row) g := by sorry
