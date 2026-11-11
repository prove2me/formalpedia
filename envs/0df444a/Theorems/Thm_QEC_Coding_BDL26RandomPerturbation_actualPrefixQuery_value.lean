-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualPrefixQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.actualPrefixQuery_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:27:19.345978+00:00
-- url     : https://prove2.me/theorems/19e42bb8-373d-474c-ac79-beab2eee098b
-- title:
--   BDL26 Random Perturbation: actual Prefix Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the actual Prefix Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L121-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ActualExecutionCost.lean#L121-L126

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

theorem QEC.Coding.BDL26RandomPerturbation.actualPrefixQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    statePoints (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T n).1 =
      assignment T (counters (eventSupport P J r) (eventBad P J r lambda K) T n) := by sorry
