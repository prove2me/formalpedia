-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initial_value
-- name    : QEC.Coding.BDL26NativeStateRows.initial_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:42:32.467202+00:00
-- url     : https://prove2.me/theorems/1fc82b40-67e7-4f61-874b-8e13f171e644
-- title:
--   BDL26 Native State Rows: initial value
-- statement:
--   The BDL26 Native State Rows construction uses the initial value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L212-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L212-L213

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

theorem QEC.Coding.BDL26NativeStateRows.initial_value {A : Type*} (T : Samples A) (L : List A) :
    (initialQ T L).value=rowsFor L T (fun _ => 0) := by sorry
