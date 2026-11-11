-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedMasterCandidateQuery_original
-- name    : QEC.Coding.BDL26RandomPerturbation.countedMasterCandidateQuery_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:08:22.292062+00:00
-- url     : https://prove2.me/theorems/7f215bfd-5c4d-469e-9613-71a51c829a5c
-- title:
--   BDL26 Random Perturbation: counted Master Candidate Query original
-- statement:
--   The BDL26 Random Perturbation construction uses the counted Master Candidate Query original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L273-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L273-L291

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

theorem QEC.Coding.BDL26RandomPerturbation.countedMasterCandidateQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) {r : ℝ} (hr : 0 ≤ r) (L : List (Triangle P)) :
    countedMasterCandidateQuery P J r L =
      ((candidateEventQuery P J hr L).1.map (eventToMaster P J r),
        (candidateEventQuery P J hr L).2) := by sorry
