-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_execute_read
-- name    : QEC.Coding.BDL26NativeStateRows.execute_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:28:00.069557+00:00
-- url     : https://prove2.me/theorems/2aff501a-d6f9-4ac2-9ee7-cd71700453a4
-- title:
--   BDL26 Native State Rows: execute read
-- statement:
--   The BDL26 Native State Rows construction uses the execute read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L536-L541
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L536-L541

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

theorem QEC.Coding.BDL26NativeStateRows.execute_read (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) (a : Index S n) :
    (readQ a (executeQ S n T trace).value).value=
      (traceCounters trace (fun _ => 0) a,T (a,traceCounters trace (fun _ => 0) a)) := by sorry
