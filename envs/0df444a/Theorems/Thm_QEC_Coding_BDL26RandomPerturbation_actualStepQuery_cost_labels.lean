-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualStepQuery_cost_labels
-- name    : QEC.Coding.BDL26RandomPerturbation.actualStepQuery_cost_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:11:39.370551+00:00
-- url     : https://prove2.me/theorems/e5fa7a8c-8bfe-4f19-8aef-7f30f0e0a880
-- title:
--   BDL26 Random Perturbation: actual Step Query cost labels
-- statement:
--   The BDL26 Random Perturbation construction uses the actual Step Query cost labels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L623-L636
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L623-L636

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

theorem QEC.Coding.BDL26RandomPerturbation.actualStepQuery_cost_labels (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r lambda : ℝ) (K : ℕ) (events : List (Event P J r))
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P)
    (hR : R.map Prod.fst = vertexInputList P) :
    (actualStepQuery P J r lambda K events T R).2 =
      (actualScanQuery P J r lambda K events R).2 +
        match (actualScanQuery P J r lambda K events R).1.map (eventToMaster P J r) with
        | none => 0
        | some e => countedMasterRefreshCost P e := by sorry
