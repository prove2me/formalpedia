-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_materializeRows_labels_nodup
-- name    : QEC.Coding.BDL26ReplacementMaterialization.materializeRows_labels_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:55:32.144701+00:00
-- url     : https://prove2.me/theorems/bf1f2a53-dabc-4f4b-89e3-60ac7ce35256
-- title:
--   BDL26 Replacement Materialization: materialize Rows labels nodup
-- statement:
--   The BDL26 Replacement Materialization construction uses the materialize Rows labels nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L805-L809
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L805-L809

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

theorem QEC.Coding.BDL26ReplacementMaterialization.materializeRows_labels_nodup {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    (((materializeRows p n R).1).map Prod.fst).Nodup := by sorry
