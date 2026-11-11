-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualScanQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.actualScanQuery_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:03:57.498627+00:00
-- url     : https://prove2.me/theorems/c517fc32-0e69-4f0a-a7d6-9baf6b07be3e
-- title:
--   BDL26 Random Perturbation: actual Scan Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the actual Scan Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L41-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L41-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPreprocessingCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26RandomPerturbation.actualScanQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P)) (R : StateRows P)
    (hR : StateRowsRep P T c R) :
    (actualScanQuery P J r lambda K (eventUniverseQuery P J hr).1 R).1 =
      select (localEvent (X := fun _ : Vertex P => Space) (eventSupport P J r) (eventBad P J r lambda K)) (assignment T c) := by sorry
