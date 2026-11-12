-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_anchorFold_min
-- name    : QEC.Coding.BDL26NativeKeyExecutionBridge.anchorFold_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:48:52.044885+00:00
-- url     : https://prove2.me/theorems/85a7e678-7f4a-4339-af6e-7caa70be5921
-- title:
--   BDL26 Native Key Execution Bridge: anchor Fold min
-- statement:
--   The BDL26 Native Key Execution Bridge construction uses the anchor Fold min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L558-L577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L558-L577

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

theorem QEC.Coding.BDL26NativeKeyExecutionBridge.anchorFold_min (a : MD.Code) (L : List MD.Code) :
    ∀ c ∈ a::L, 2*(anchorFoldQ a L).1.owner+(anchorFoldQ a L).1.copy ≤ 2*c.owner+c.copy := by sorry
