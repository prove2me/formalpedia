-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_emitted_value
-- name    : QEC.Coding.BDL26NativeStateRows.original_emitted_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:52:34.551021+00:00
-- url     : https://prove2.me/theorems/8bfc47f2-43f2-4cd7-ae3d-396d8a5334d8
-- title:
--   BDL26 Native State Rows: original emitted value
-- statement:
--   Every emitted native-labelled coordinate is the same original table read
--   at its actual original execution counter, in the preserved native order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L801-L808
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L801-L808

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

theorem QEC.Coding.BDL26NativeStateRows.original_emitted_value (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ) :
    (emittedQ S n (encodeSamples S n T) (originalTrace S n J r lambda K T m)).value=
      (indices (count S n)).map (fun a => (a,assignment (X := fun _ : Vertex (P S n) => Space) (asTable T)
        (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K) (asTable T) m)
        (decode S n a))) := by sorry
