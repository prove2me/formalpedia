-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_map_operations
-- name    : QEC.Coding.BDL26NativeStateRows.map_operations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:32:37.841056+00:00
-- url     : https://prove2.me/theorems/ce1c8772-42a9-4726-bfe4-8ca6525fe983
-- title:
--   BDL26 Native State Rows: map operations
-- statement:
--   The BDL26 Native State Rows construction uses the map operations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L44-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L44-L53

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

theorem QEC.Coding.BDL26NativeStateRows.map_operations {A B : Type*} (f : A → Run B) (L : List A) (c : ℕ)
    (hc : ∀ a∈L,(f a).operations≤c) :
    (mapQ f L).operations≤L.length*(c+3) := by sorry
