-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedMasterUniverseQuery_original
-- name    : QEC.Coding.BDL26RandomPerturbation.countedMasterUniverseQuery_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:12:32.811359+00:00
-- url     : https://prove2.me/theorems/69aa9655-6425-4c4f-b5aa-a98aabdb03ed
-- title:
--   BDL26 Random Perturbation: counted Master Universe Query original
-- statement:
--   Full preprocessing conjugacy: original tuples, multiplicities, duplicate
--   removal, rank comparisons, final list order, and numeric preprocessing cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L330-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L330-L338

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

theorem QEC.Coding.BDL26RandomPerturbation.countedMasterUniverseQuery_original (P : TannerSquarePresentation)
    (J : Vertex P → Space) {r : ℝ} (hr : 0 ≤ r) :
    countedMasterUniverseQuery P J r =
      ((eventUniverseQuery P J hr).1.map (eventToMaster P J r),
        (eventUniverseQuery P J hr).2) := by sorry
