-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_execute_labels_nodup
-- name    : QEC.Coding.BDL26NativeStateRows.execute_labels_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:46:58.961734+00:00
-- url     : https://prove2.me/theorems/8d40b1e5-7f82-42c3-99d4-31016f2377bc
-- title:
--   BDL26 Native State Rows: execute labels nodup
-- statement:
--   The BDL26 Native State Rows construction uses the execute labels nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L530-L534
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L530-L534

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

theorem QEC.Coding.BDL26NativeStateRows.execute_labels_nodup (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    ((executeQ S n T trace).value.map Prod.fst).Nodup := by sorry
