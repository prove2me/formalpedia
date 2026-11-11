-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_StateRowsRep_rows
-- name    : QEC.Coding.BDL26RandomPerturbation.StateRowsRep_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:24:56.743115+00:00
-- url     : https://prove2.me/theorems/fcc76a84-df34-4225-957e-05426c9e98fe
-- title:
--   BDL26 Random Perturbation: State Rows Rep rows
-- statement:
--   A represented row list is exactly the fixed input-label list with its actual
--   counter and sample addresses. This is stronger than equality of emitted points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L354-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L354-L368

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

theorem QEC.Coding.BDL26RandomPerturbation.StateRowsRep_rows (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P))
    (R : StateRows P) (hR : StateRowsRep P T c R) :
    R = (vertexInputList P).map (fun v => (v, c v, T (v, c v))) := by sorry
