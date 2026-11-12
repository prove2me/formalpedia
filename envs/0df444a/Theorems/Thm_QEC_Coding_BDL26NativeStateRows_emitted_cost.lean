-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_emitted_cost
-- name    : QEC.Coding.BDL26NativeStateRows.emitted_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:48:59.715029+00:00
-- url     : https://prove2.me/theorems/b3713f43-f46a-41b8-95d9-8790974b16fb
-- title:
--   BDL26 Native State Rows: emitted cost
-- statement:
--   The BDL26 Native State Rows construction uses the emitted cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L595-L605
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L595-L605

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

theorem QEC.Coding.BDL26NativeStateRows.emitted_cost (S : OddScale) (n : ℕ) (T : Samples (Index S n))
    (trace : List (List (Index S n))) :
    (emittedQ S n T trace).operations=(executeQ S n T trace).operations+5*count S n+1 ∧
    (emittedQ S n T trace).allocations=(executeQ S n T trace).allocations+2*count S n+1 := by sorry
