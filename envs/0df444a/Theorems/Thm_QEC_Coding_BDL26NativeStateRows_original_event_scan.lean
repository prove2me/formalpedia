-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeStateRows_original_event_scan
-- name    : QEC.Coding.BDL26NativeStateRows.original_event_scan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:50:08.284757+00:00
-- url     : https://prove2.me/theorems/dbe932b3-e2fb-49d5-b335-8a236c310d05
-- title:
--   BDL26 Native State Rows: original event scan
-- statement:
--   Every supplied original event scan, including empty/repeated labels, is
--   identified. Native row order cannot change which original event is first.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L753-L780
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeStateRows.lean#L753-L780

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

theorem QEC.Coding.BDL26NativeStateRows.original_event_scan (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : Samples (Vertex (P S n))) (m : ℕ)
    (L : List (Event (P S n) J r)) :
    firstBadFrom (localEvent
      (BDL26RandomPerturbation.VariableRelabeling.pulledSupport (P S n) J r (decode S n))
      (BDL26RandomPerturbation.VariableRelabeling.pulledBad (P S n) J r lambda K (decode S n))) L
      (points S n (executeQ S n (encodeSamples S n T)
        (originalTrace S n J r lambda K T m)).value)=
      firstBadFrom (localEvent (eventSupport (P S n) J r)
        (eventBad (P S n) J r lambda K)) L
        (assignment (X := fun _ : Vertex (P S n) => Space) (asTable T) (counters (X := fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
          (eventBad (P S n) J r lambda K) (asTable T) m)) := by sorry
