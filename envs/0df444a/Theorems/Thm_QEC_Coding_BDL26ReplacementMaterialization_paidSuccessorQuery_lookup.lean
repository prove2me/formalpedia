-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_paidSuccessorQuery_lookup
-- name    : QEC.Coding.BDL26ReplacementMaterialization.paidSuccessorQuery_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:52:22.877014+00:00
-- url     : https://prove2.me/theorems/2fe139f8-6b5a-4247-9f24-a580fbcc273d
-- title:
--   BDL26 Replacement Materialization: paid Successor Query lookup
-- statement:
--   The BDL26 Replacement Materialization construction uses the paid Successor Query lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L775-L779
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L775-L779

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

theorem QEC.Coding.BDL26ReplacementMaterialization.paidSuccessorQuery_lookup {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) (v : Vertex (StagePresentation p (n+1))) :
    (pointRowQuery v (paidSuccessorQuery p n J T).1).1 = physicalSuccessorOutput p n J T v := by sorry
