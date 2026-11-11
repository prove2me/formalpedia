-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_joint_actualExecutionCost
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_joint_actualExecutionCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:14:08.958224+00:00
-- url     : https://prove2.me/theorems/1aca33e3-0df4-488a-aaff-9d55fc7c9481
-- title:
--   BDL26 Random Perturbation: measurable joint actual Execution Cost
-- statement:
--   The original stopped numeric cost is jointly measurable, with infinity on
--   nontermination and the original halt-time zero default left unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L691-L729
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L691-L729

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_joint_actualExecutionCost (P : TannerSquarePresentation)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      actualExecutionCost P w.1 hr lambda K w.2) := by sorry
