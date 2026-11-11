-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_totalMaterializationCost_succ
-- name    : QEC.Coding.BDL26ReplacementMaterialization.totalMaterializationCost_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:44:54.328172+00:00
-- url     : https://prove2.me/theorems/e6f04c61-0139-47a0-ac66-e696185d2658
-- title:
--   BDL26 Replacement Materialization: total Materialization Cost succ
-- statement:
--   The BDL26 Replacement Materialization construction uses the total Materialization Cost succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L611-L616
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L611-L616

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

theorem QEC.Coding.BDL26ReplacementMaterialization.totalMaterializationCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p (N+1)) :
    totalMaterializationCost p (N+1) z = totalMaterializationCost p N z.1 +
      materializationCost p N (evaluate p N z.1,z.2) := by sorry
