-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualScanQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.actualScanQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:02:58.770218+00:00
-- url     : https://prove2.me/theorems/f898d165-38a7-434a-80e3-4ae0fbaba3fd
-- title:
--   BDL26 Random Perturbation: actual Scan Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the actual Scan Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L128-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L128-L138

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

theorem QEC.Coding.BDL26RandomPerturbation.actualScanQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r)) (R : StateRows P) :
    (actualScanQuery P J r lambda K events R).2 ≤
      events.length*(stateQueryBudget (Fintype.card (Triangle P)) R.length K+1) := by sorry
