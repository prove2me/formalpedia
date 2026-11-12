-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_trace_labels
-- name    : QEC.Coding.BDL26NativeStateRows.trace_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:45:13.925722+00:00
-- url     : https://prove2.me/theorems/9543ae45-a26a-42b7-a53c-defca6b245ec
-- title:
--   BDL26 Native State Rows: trace labels
-- statement:
--   The BDL26 Native State Rows construction uses the trace labels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L408-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L408-L413

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

theorem QEC.Coding.BDL26NativeStateRows.trace_labels {A : Type*} [DecidableEq A] (T : Samples A)
    (R : Rows A) (trace : List (List A)) :
    (runFromQ T R trace).value.map Prod.fst=R.map Prod.fst := by sorry
