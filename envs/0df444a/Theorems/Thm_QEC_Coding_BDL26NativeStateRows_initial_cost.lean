-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initial_cost
-- name    : QEC.Coding.BDL26NativeStateRows.initial_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:43:56.775081+00:00
-- url     : https://prove2.me/theorems/123805bf-79a8-4383-b422-08ee8242cdd2
-- title:
--   BDL26 Native State Rows: initial cost
-- statement:
--   The BDL26 Native State Rows construction uses the initial cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L215-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L215-L222

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

theorem QEC.Coding.BDL26NativeStateRows.initial_cost {A : Type*} (T : Samples A) (L : List A) :
    (initialQ T L).operations=9*L.length ∧
      (initialQ T L).allocations=2*L.length := by sorry
