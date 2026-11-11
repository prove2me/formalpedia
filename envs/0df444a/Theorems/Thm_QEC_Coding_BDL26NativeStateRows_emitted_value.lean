-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_emitted_value
-- name    : QEC.Coding.BDL26NativeStateRows.emitted_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:43:15.011815+00:00
-- url     : https://prove2.me/theorems/46c3a42b-5c6e-4866-92d8-6e9f2432275d
-- title:
--   BDL26 Native State Rows: emitted value
-- statement:
--   The BDL26 Native State Rows construction uses the emitted value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L587-L593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L587-L593

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

theorem QEC.Coding.BDL26NativeStateRows.emitted_value (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (emittedQ S n T trace).value=(indices (count S n)).map
      (fun a => (a,T (a,traceCounters trace (fun _ => 0) a))) := by sorry
