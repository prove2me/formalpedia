-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_stageVertices_le_qubits
-- name    : QEC.Coding.BDL26ReplacementMaterialization.stageVertices_le_qubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:16:46.929989+00:00
-- url     : https://prove2.me/theorems/5b2d6c56-f6aa-4d66-ad92-7e103ef87261
-- title:
--   BDL26 Replacement Materialization: stage Vertices le qubits
-- statement:
--   The BDL26 Replacement Materialization construction uses the stage Vertices le qubits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L627-L633
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L627-L633

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

theorem QEC.Coding.BDL26ReplacementMaterialization.stageVertices_le_qubits {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Fintype.card (Vertex (StagePresentation p n)) ≤ 65*stageQubits p n := by sorry
