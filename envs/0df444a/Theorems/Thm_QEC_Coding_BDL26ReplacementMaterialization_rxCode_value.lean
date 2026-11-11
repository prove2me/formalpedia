-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_rxCode_value
-- name    : QEC.Coding.BDL26ReplacementMaterialization.rxCode_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:11:58.791181+00:00
-- url     : https://prove2.me/theorems/20f53531-3d22-4c3f-95f6-16ee637972d9
-- title:
--   BDL26 Replacement Materialization: rx Code value
-- statement:
--   The BDL26 Replacement Materialization construction uses the rx Code value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L341-L346
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L341-L346

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

theorem QEC.Coding.BDL26ReplacementMaterialization.rxCode_value (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → Space)
    (v : Vertex (rxReplacementPresentation P S)) : (rxCode P S v).eval J = rxVertexPoint P S J v := by sorry
