-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedStageCost_nonhalting
-- name    : QEC.Coding.BDL26ReplacementMaterialization.extendedStageCost_nonhalting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:49:22.345527+00:00
-- url     : https://prove2.me/theorems/92ec5cba-837e-429c-aeab-f3a3a940b06c
-- title:
--   BDL26 Replacement Materialization: extended Stage Cost nonhalting
-- statement:
--   The BDL26 Replacement Materialization construction uses the extended Stage Cost nonhalting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L726-L729
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L726-L729

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

theorem QEC.Coding.BDL26ReplacementMaterialization.extendedStageCost_nonhalting {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : ¬ stageHalts p N i z) :
    extendedStageCost p N i z = ∞ := by sorry
