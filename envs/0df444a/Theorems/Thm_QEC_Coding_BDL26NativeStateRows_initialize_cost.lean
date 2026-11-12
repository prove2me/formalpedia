-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_initialize_cost
-- name    : QEC.Coding.BDL26NativeStateRows.initialize_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:19:22.962422+00:00
-- url     : https://prove2.me/theorems/6b5f0ba0-781c-4f78-9427-cbf8eb28adad
-- title:
--   BDL26 Native State Rows: initialize cost
-- statement:
--   The BDL26 Native State Rows construction uses the initialize cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L482-L509
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L482-L509

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

theorem QEC.Coding.BDL26NativeStateRows.initialize_cost (S : OddScale) (n : ℕ) (T : Samples (Index S n)) :
    (initializeQ S n T).operations=
      (BDL26NativePresentationGenerator.setupQ S n).2+2*(count S n)^2+12*count S n+4 ∧
    (initializeQ S n T).allocations≤
      BDL26NativePresentationGenerator.allocatedRecords S n+(count S n)^2+2*count S n+1 := by sorry
