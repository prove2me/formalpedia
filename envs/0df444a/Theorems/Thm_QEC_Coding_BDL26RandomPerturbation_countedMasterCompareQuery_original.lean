-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedMasterCompareQuery_original
-- name    : QEC.Coding.BDL26RandomPerturbation.countedMasterCompareQuery_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:06:15.765544+00:00
-- url     : https://prove2.me/theorems/4bed8d0a-f738-43bc-ac6f-39af310e4d75
-- title:
--   BDL26 Random Perturbation: counted Master Compare Query original
-- statement:
--   The BDL26 Random Perturbation construction uses the counted Master Compare Query original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L234-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L234-L237

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

theorem QEC.Coding.BDL26RandomPerturbation.countedMasterCompareQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r : ℝ) (e f : Event P J r) :
    countedMasterCompareQuery P (eventToMaster P J r e) (eventToMaster P J r f) =
      eventCompareQuery P J r e f := by sorry
