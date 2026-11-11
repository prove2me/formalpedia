-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualStepQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.actualStepQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:05:05.339879+00:00
-- url     : https://prove2.me/theorems/a2812492-ad8a-4e7a-8812-b23c02f0b0a3
-- title:
--   BDL26 Random Perturbation: actual Step Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the actual Step Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L140-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L140-L153

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

theorem QEC.Coding.BDL26RandomPerturbation.actualStepQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (events : List (Event P J r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P) :
    (actualStepQuery P J r lambda K events T R).2 ≤
      events.length*(stateQueryBudget (Fintype.card (Triangle P)) R.length K+1)+378+32*R.length := by sorry
