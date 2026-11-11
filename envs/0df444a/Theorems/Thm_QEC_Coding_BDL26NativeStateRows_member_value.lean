-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_member_value
-- name    : QEC.Coding.BDL26NativeStateRows.member_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:35:01.62234+00:00
-- url     : https://prove2.me/theorems/7409147f-2686-44a1-b9a0-50c4709615ef
-- title:
--   BDL26 Native State Rows: member value
-- statement:
--   The BDL26 Native State Rows construction uses the member value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L297-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L297-L301

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

theorem QEC.Coding.BDL26NativeStateRows.member_value {A : Type*} [DecidableEq A] (a : A) (L : List A) :
    (memberQ a L).value=true ↔ a∈L := by sorry
