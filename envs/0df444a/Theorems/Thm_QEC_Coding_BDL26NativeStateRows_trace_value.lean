-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_trace_value
-- name    : QEC.Coding.BDL26NativeStateRows.trace_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:40:49.360174+00:00
-- url     : https://prove2.me/theorems/8c89e6f6-bc7f-4ec1-8fff-8b18df0d4f6d
-- title:
--   BDL26 Native State Rows: trace value
-- statement:
--   The BDL26 Native State Rows construction uses the trace value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L398-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L398-L406

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeStateRows
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem QEC.Coding.BDL26NativeStateRows.trace_value {A : Type*} [DecidableEq A] (T : Samples A)
    (L : List A) (trace : List (List A)) (c : A → ℕ) :
    (runFromQ T (rowsFor L T c) trace).value=rowsFor L T (traceCounters trace c) := by sorry
