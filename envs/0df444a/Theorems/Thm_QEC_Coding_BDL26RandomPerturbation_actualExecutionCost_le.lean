-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualExecutionCost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.actualExecutionCost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:06:06.074396+00:00
-- url     : https://prove2.me/theorems/699ec068-c8cd-410f-a48d-092e6d998f42
-- title:
--   BDL26 Random Perturbation: actual Execution Cost le
-- statement:
--   This bound is derived from the counted program, not stored as an execution field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L184-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L184-L211

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

theorem QEC.Coding.BDL26RandomPerturbation.actualExecutionCost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space))
    (hT : Halts (eventSupport P J r) (eventBad P J r lambda K) T) :
    actualExecutionCost P J hr lambda K T ≤
      (eventUniverseBudget (Fintype.card (Triangle P))+54*Fintype.card (Vertex P)+
        Fintype.card (Triangle P)^4*(stateQueryBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P)) K+1) : ℕ)+
      ((Fintype.card (Triangle P)^4*(stateQueryBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P)) K+1)+378+32*Fintype.card (Vertex P) : ℕ) : ℝ≥0∞)*
        totalSteps (eventSupport P J r) (eventBad P J r lambda K) T := by sorry
