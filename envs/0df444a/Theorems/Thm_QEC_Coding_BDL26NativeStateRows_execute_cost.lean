-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_execute_cost
-- name    : QEC.Coding.BDL26NativeStateRows.execute_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:51:01.042983+00:00
-- url     : https://prove2.me/theorems/0491965f-fbc7-4fba-961a-863db8b562d8
-- title:
--   BDL26 Native State Rows: execute cost
-- statement:
--   The BDL26 Native State Rows construction uses the execute cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L543-L562
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L543-L562

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

theorem QEC.Coding.BDL26NativeStateRows.execute_cost (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (executeQ S n T trace).operations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        2*(count S n)^2+12*count S n+6+2*trace.length+
        count S n*(2*traceWeight trace+11*trace.length) ∧
    (executeQ S n T trace).allocations≤
      (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220+
        (count S n)^2+2*count S n+2+2*count S n*trace.length := by sorry
