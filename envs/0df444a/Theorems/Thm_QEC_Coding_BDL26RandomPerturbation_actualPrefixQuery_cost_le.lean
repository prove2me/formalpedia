-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualPrefixQuery_cost_le
-- name    : QEC.Coding.BDL26RandomPerturbation.actualPrefixQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:05:20.721569+00:00
-- url     : https://prove2.me/theorems/0fddce2b-1550-465a-b123-5365ac1aa230
-- title:
--   BDL26 Random Perturbation: actual Prefix Query cost le
-- statement:
--   The BDL26 Random Perturbation construction uses the actual Prefix Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L155-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L155-L168

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

theorem QEC.Coding.BDL26RandomPerturbation.actualPrefixQuery_cost_le (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T n).2 ≤ 5*Fintype.card (Vertex P)+
      n*((eventUniverseQuery P J hr).1.length*(stateQueryBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P)) K+1)+378+32*Fintype.card (Vertex P)) := by sorry
