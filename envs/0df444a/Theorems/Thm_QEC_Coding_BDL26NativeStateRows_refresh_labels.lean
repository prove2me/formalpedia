-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_refresh_labels
-- name    : QEC.Coding.BDL26NativeStateRows.refresh_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:23:25.166858+00:00
-- url     : https://prove2.me/theorems/240a58dd-a24c-4f19-be7a-57982eb3ec0b
-- title:
--   BDL26 Native State Rows: refresh labels
-- statement:
--   The BDL26 Native State Rows construction uses the refresh labels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L356-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L356-L361

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

theorem QEC.Coding.BDL26NativeStateRows.refresh_labels {A : Type*} [DecidableEq A] (T : Samples A)
    (U : List A) (R : Rows A) : (refreshQ T U R).value.map Prod.fst=R.map Prod.fst := by sorry
