-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_actualScanQuery_prefix
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_actualScanQuery_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:27:40.041346+00:00
-- url     : https://prove2.me/theorems/eb7fd90e-3899-4e1c-ba74-4371f1a7bd9c
-- title:
--   BDL26 Random Perturbation: measurable actual Scan Query prefix
-- statement:
--   Joint row data come from the original counters and original table addresses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L639-L658
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L639-L658

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

theorem QEC.Coding.BDL26RandomPerturbation.measurable_actualScanQuery_prefix (P : TannerSquarePresentation)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K n : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let events := (eventUniverseQuery P w.1 hr).1
      let R := (actualPrefixQuery P w.1 r lambda K events w.2 n).1
      let q := actualScanQuery P w.1 r lambda K events R
      (q.1.map (eventToMaster P w.1 r), q.2)) := by sorry
