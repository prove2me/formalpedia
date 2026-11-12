-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_execute_value
-- name    : QEC.Coding.BDL26NativeStateRows.execute_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:19:04.015248+00:00
-- url     : https://prove2.me/theorems/c305d950-905b-4f2e-a22f-641c8c55e40d
-- title:
--   BDL26 Native State Rows: execute value
-- statement:
--   The BDL26 Native State Rows construction uses the execute value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L517-L523
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L517-L523

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

theorem QEC.Coding.BDL26NativeStateRows.execute_value (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (executeQ S n T trace).value=
      rowsFor (indices (count S n)) T (traceCounters trace (fun _ => 0)) := by sorry
