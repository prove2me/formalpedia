-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_trace_counters_append
-- name    : QEC.Coding.BDL26NativeStateRows.trace_counters_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:21:34.321948+00:00
-- url     : https://prove2.me/theorems/c806c73c-ea25-4d04-8d98-e7e3ee434fea
-- title:
--   BDL26 Native State Rows: trace counters append
-- statement:
--   The BDL26 Native State Rows construction uses the trace counters append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L434-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L434-L439

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

theorem QEC.Coding.BDL26NativeStateRows.trace_counters_append {A : Type*} [DecidableEq A]
    (left right : List (List A)) (c : A → ℕ) :
    traceCounters (left++right) c=traceCounters right (traceCounters left c) := by sorry
