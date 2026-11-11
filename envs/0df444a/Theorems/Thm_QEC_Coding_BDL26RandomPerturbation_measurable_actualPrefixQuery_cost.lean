-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_actualPrefixQuery_cost
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_actualPrefixQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:15:03.891215+00:00
-- url     : https://prove2.me/theorems/834008a6-ba7f-4457-98b8-072d2d1277fa
-- title:
--   BDL26 Random Perturbation: measurable actual Prefix Query cost
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable actual Prefix Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L675-L687
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L675-L687

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_actualPrefixQuery_cost (P : TannerSquarePresentation)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K n : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      (actualPrefixQuery P w.1 r lambda K (eventUniverseQuery P w.1 hr).1 w.2 n).2) := by sorry
