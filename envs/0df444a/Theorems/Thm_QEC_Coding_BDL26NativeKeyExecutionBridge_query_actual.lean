-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_query_actual
-- name    : QEC.Coding.BDL26NativeKeyExecutionBridge.query_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:49:02.395096+00:00
-- url     : https://prove2.me/theorems/aa3590be-383a-463e-909f-385dfe8ec89f
-- title:
--   BDL26 Native Key Execution Bridge: query actual
-- statement:
--   The BDL26 Native Key Execution Bridge construction uses the query actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L644-L665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L644-L665

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

theorem QEC.Coding.BDL26NativeKeyExecutionBridge.query_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r lambda : ℝ) (K : ℕ)
    (row : LiveRow S n J r) (R : SR.Rows (SR.Index S n)) :
    (eventQueryQ S n J r lambda K row R).1 = true ↔
      originalPoints S n R ∈ localEvent
        (keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r)
        (keyBad (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
          J r lambda K) (event S n J r row) := by sorry
