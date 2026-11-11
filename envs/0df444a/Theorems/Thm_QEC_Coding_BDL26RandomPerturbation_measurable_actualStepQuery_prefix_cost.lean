-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_actualStepQuery_prefix_cost
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_actualStepQuery_prefix_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:13:11.727652+00:00
-- url     : https://prove2.me/theorems/0da84eea-f08d-4ec4-b1f8-2042581ba43d
-- title:
--   BDL26 Random Perturbation: measurable actual Step Query prefix cost
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable actual Step Query prefix cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L660-L673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L660-L673

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_actualStepQuery_prefix_cost (P : TannerSquarePresentation)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K n : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let events := (eventUniverseQuery P w.1 hr).1
      let R := (actualPrefixQuery P w.1 r lambda K events w.2 n).1
      (actualStepQuery P w.1 r lambda K events w.2 R).2) := by sorry
