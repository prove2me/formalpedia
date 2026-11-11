-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_value
-- name    : QEC.Coding.BDL26NativeStateRows.initialize_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:19:43.763552+00:00
-- url     : https://prove2.me/theorems/ff3ccf37-3e7d-4797-8460-8efe177a5f00
-- title:
--   BDL26 Native State Rows: initialize value
-- statement:
--   The BDL26 Native State Rows construction uses the initialize value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L472-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L472-L476

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

theorem QEC.Coding.BDL26NativeStateRows.initialize_value (S : OddScale) (n : ℕ) (T : Samples (Index S n)) :
    (initializeQ S n T).value=rowsFor (indices (count S n)) T (fun _ => 0) := by sorry
