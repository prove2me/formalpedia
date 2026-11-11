-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_countedMasterUniverseQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_countedMasterUniverseQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:12:18.256438+00:00
-- url     : https://prove2.me/theorems/aefc44dd-a70e-4c9a-9cf5-1064f3933ea1
-- title:
--   BDL26 Random Perturbation: measurable counted Master Universe Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable counted Master Universe Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L340-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L340-L350

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
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton

theorem QEC.Coding.BDL26RandomPerturbation.measurable_countedMasterUniverseQuery (P : TannerSquarePresentation) (r : ℝ) :
    Measurable (fun J : Vertex P → Space => countedMasterUniverseQuery P J r) := by sorry
