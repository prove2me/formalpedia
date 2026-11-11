-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_pointSnapshotQuery_cost
-- name    : QEC.Coding.BDL26RandomPerturbation.pointSnapshotQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:07:26.063564+00:00
-- url     : https://prove2.me/theorems/d509286f-8a77-4383-b9d8-ca039f1ebcf7
-- title:
--   BDL26 Random Perturbation: point Snapshot Query cost
-- statement:
--   Snapshot arithmetic has this exact cost on every input, including zeroes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L386-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L386-L387

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

theorem QEC.Coding.BDL26RandomPerturbation.pointSnapshotQuery_cost (lambda : ℝ) (a b : Space) :
    (pointSnapshotQuery lambda a b).2 = 24 := by sorry
