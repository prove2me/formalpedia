-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_trace_cost
-- name    : QEC.Coding.BDL26NativeStateRows.trace_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:39:34.288841+00:00
-- url     : https://prove2.me/theorems/0346a52f-30e2-462a-a7c5-0f80ed81f85b
-- title:
--   BDL26 Native State Rows: trace cost
-- statement:
--   The BDL26 Native State Rows construction uses the trace cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L420-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L420-L432

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

theorem QEC.Coding.BDL26NativeStateRows.trace_cost {A : Type*} [DecidableEq A] (T : Samples A)
    (R : Rows A) (trace : List (List A)) :
    (runFromQ T R trace).operations≤2*trace.length+1+
      R.length*(2*traceWeight trace+11*trace.length) ∧
    (runFromQ T R trace).allocations≤2*R.length*trace.length := by sorry
