-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_refreshStateRowsQuery_cost_labels
-- name    : QEC.Coding.BDL26RandomPerturbation.refreshStateRowsQuery_cost_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:25:52.269964+00:00
-- url     : https://prove2.me/theorems/968383aa-90bf-4382-9fe8-d135c2bde360
-- title:
--   BDL26 Random Perturbation: refresh State Rows Query cost labels
-- statement:
--   Refresh cost uses exactly the original support traversal and stored row labels;
--   the new sample values and counter magnitudes do not change that traversal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L601-L616
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountedCostMeasurability.lean#L601-L616

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

theorem QEC.Coding.BDL26RandomPerturbation.refreshStateRowsQuery_cost_labels (P : TannerSquarePresentation)
    (J : Vertex P → Space) (r : ℝ) (e : Event P J r)
    (T : Table (X := fun _ : Vertex P => Space)) (R : StateRows P)
    (hR : R.map Prod.fst = vertexInputList P) :
    (refreshStateRowsQuery P J r e T R).2 =
      countedMasterRefreshCost P (eventToMaster P J r e) := by sorry
