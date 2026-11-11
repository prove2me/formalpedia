-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_read_rowsFor
-- name    : QEC.Coding.BDL26NativeStateRows.read_rowsFor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:17:29.812424+00:00
-- url     : https://prove2.me/theorems/2946ffab-0fce-4cd4-8e38-34ed424a8b26
-- title:
--   BDL26 Native State Rows: read rows For
-- statement:
--   The BDL26 Native State Rows construction uses the read rows For property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L280-L289
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L280-L289

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

theorem QEC.Coding.BDL26NativeStateRows.read_rowsFor {A : Type*} [DecidableEq A] (T : Samples A) (L : List A)
    (c : A → ℕ) (a : A) (ha : a∈L) :
    (readQ a (rowsFor L T c)).value=(c a,T (a,c a)) := by sorry
