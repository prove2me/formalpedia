-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_trace_counters
-- name    : QEC.Coding.BDL26NativeStateRows.original_trace_counters
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:40:18.794212+00:00
-- url     : https://prove2.me/theorems/d2c203af-bf51-43c1-82d4-6be5c302d954
-- title:
--   BDL26 Native State Rows: original trace counters
-- statement:
--   The BDL26 Native State Rows construction uses the original trace counters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L686-L704
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L686-L704

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
noncomputable section
open scoped Classical
open QEC.Coding.ProbabilisticConstruction

theorem QEC.Coding.BDL26NativeStateRows.original_trace_counters (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    traceCounters (originalTrace S n J r lambda K T m) (fun _ => 0)=
      fun a => counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m (decode S n a) := by sorry
