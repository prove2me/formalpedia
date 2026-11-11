-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_refresh_cost
-- name    : QEC.Coding.BDL26NativeStateRows.refresh_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:26:13.728367+00:00
-- url     : https://prove2.me/theorems/59a05338-543f-4315-80b7-384cef3f7d15
-- title:
--   BDL26 Native State Rows: refresh cost
-- statement:
--   The BDL26 Native State Rows construction uses the refresh cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L371-L378
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L371-L378

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

theorem QEC.Coding.BDL26NativeStateRows.refresh_cost {A : Type*} [DecidableEq A] (T : Samples A)
    (U : List A) (R : Rows A) :
    (refreshQ T U R).operations≤R.length*(2*U.length+11) ∧
      (refreshQ T U R).allocations≤2*R.length := by sorry
