-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_countedMasterScan_original
-- name    : QEC.Coding.BDL26RandomPerturbation.countedMasterScan_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:11:05.335165+00:00
-- url     : https://prove2.me/theorems/11227d40-8a72-43c4-8d60-f1e8ef099e57
-- title:
--   BDL26 Random Perturbation: counted Master Scan original
-- statement:
--   Fixed-carrier scan conjugacy includes numeric costs and the original priority.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L519-L528
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L519-L528

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

theorem QEC.Coding.BDL26RandomPerturbation.countedMasterScan_original (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (R : StateRows P) :
    scanQuery (countedMasterStateEventQuery P J lambda K)
        (countedMasterUniverseQuery P J r).1 R =
      ((actualScanQuery P J r lambda K (eventUniverseQuery P J hr).1 R).1.map
          (eventToMaster P J r),
        (actualScanQuery P J r lambda K (eventUniverseQuery P J hr).1 R).2) := by sorry
