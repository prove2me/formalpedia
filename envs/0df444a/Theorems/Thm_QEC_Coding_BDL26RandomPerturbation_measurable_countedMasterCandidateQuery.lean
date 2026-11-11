-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_countedMasterCandidateQuery
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_countedMasterCandidateQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:11:57.581276+00:00
-- url     : https://prove2.me/theorems/8211c0d0-c29d-4c09-8822-f3c123af783a
-- title:
--   BDL26 Random Perturbation: measurable counted Master Candidate Query
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable counted Master Candidate Query property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L293-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L293-L304

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_countedMasterCandidateQuery (P : TannerSquarePresentation)
    (r : ℝ) (L : List (Triangle P)) :
    Measurable (fun J : Vertex P → Space => countedMasterCandidateQuery P J r L) := by sorry
