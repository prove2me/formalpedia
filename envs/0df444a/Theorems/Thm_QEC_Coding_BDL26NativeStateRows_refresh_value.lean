-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_refresh_value
-- name    : QEC.Coding.BDL26NativeStateRows.refresh_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:19:43.428234+00:00
-- url     : https://prove2.me/theorems/9b99b577-c587-46f1-a25c-ff152de9c3c1
-- title:
--   BDL26 Native State Rows: refresh value
-- statement:
--   The BDL26 Native State Rows construction uses the refresh value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L363-L369
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L363-L369

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

theorem QEC.Coding.BDL26NativeStateRows.refresh_value {A : Type*} [DecidableEq A] (T : Samples A)
    (U L : List A) (c : A → ℕ) :
    (refreshQ T U (rowsFor L T c)).value=rowsFor L T (advanceList U c) := by sorry
