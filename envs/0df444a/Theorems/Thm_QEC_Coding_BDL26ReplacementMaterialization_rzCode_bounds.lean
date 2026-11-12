-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_rzCode_bounds
-- name    : QEC.Coding.BDL26ReplacementMaterialization.rzCode_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:11:20.018174+00:00
-- url     : https://prove2.me/theorems/53312887-e25a-4b2a-8bbd-1cb31bc7bd1a
-- title:
--   BDL26 Replacement Materialization: rz Code bounds
-- statement:
--   The BDL26 Replacement Materialization construction uses the rz Code bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L376-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L376-L385

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

theorem QEC.Coding.BDL26ReplacementMaterialization.rzCode_bounds (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (S : OddScale)
    (v : Vertex (BDL26RZLocalReplacement.rzReplacementPresentation P A S)) :
    (rzCode P A S v).reads ≤ 8 ∧ (rzCode P A S v).work ≤ 2048 := by sorry
