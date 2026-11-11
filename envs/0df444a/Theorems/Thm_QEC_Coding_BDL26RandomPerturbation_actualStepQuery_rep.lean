-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualStepQuery_rep
-- name    : QEC.Coding.BDL26RandomPerturbation.actualStepQuery_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:04:12.547954+00:00
-- url     : https://prove2.me/theorems/8ca6a6f2-1f17-40e0-8a9b-33427fdf7083
-- title:
--   BDL26 Random Perturbation: actual Step Query rep
-- statement:
--   The BDL26 Random Perturbation construction uses the actual Step Query rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L76-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L76-L108

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

theorem QEC.Coding.BDL26RandomPerturbation.actualStepQuery_rep (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P)) (R : StateRows P)
    (hR : StateRowsRep P T c R) :
    StateRowsRep P T (step (eventSupport P J r) (eventBad P J r lambda K) T c)
      (actualStepQuery P J r lambda K (eventUniverseQuery P J hr).1 T R).1 := by sorry
