-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_paid_stage_rows_history
-- name    : QEC.Coding.BDL26ReplacementMaterialization.paid_stage_rows_history
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:52:37.6832+00:00
-- url     : https://prove2.me/theorems/e01013c9-d3c4-40f1-9453-3f34d854be16
-- title:
--   BDL26 Replacement Materialization: paid stage rows history
-- statement:
--   The paid rows represent the same physical successor used in the original history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L737-L745
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L737-L745

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26ReplacementMaterialization.paid_stage_rows_history {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) :
    (paidSuccessorQuery p i.val (stageInput p N i z) (tableAt p N i z)).1 =
      (vertexInputList (StagePresentation p (i.val+1))).map
        (fun v => (v,history p N z ⟨i.val+1,by omega⟩ v)) := by sorry
