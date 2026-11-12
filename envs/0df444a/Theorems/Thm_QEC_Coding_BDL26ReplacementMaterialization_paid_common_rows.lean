-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_paid_common_rows
-- name    : QEC.Coding.BDL26ReplacementMaterialization.paid_common_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:52:41.538708+00:00
-- url     : https://prove2.me/theorems/ce36b6c5-ab59-4c02-80da-5b6becfe9f39
-- title:
--   BDL26 Replacement Materialization: paid common rows
-- statement:
--   The BDL26 Replacement Materialization construction uses the paid common rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L798-L803
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L798-L803

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

theorem QEC.Coding.BDL26ReplacementMaterialization.paid_common_rows {L : ℝ} (p : GeometricParameters L)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) (n : ℕ) :
    (paidSuccessorQuery p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)).1 =
      (vertexInputList (StagePresentation p (n+1))).map
        (fun v => (v,BDL26CountableEmbeddingExperiment.levelMap p omega (n+1) v)) := by sorry
