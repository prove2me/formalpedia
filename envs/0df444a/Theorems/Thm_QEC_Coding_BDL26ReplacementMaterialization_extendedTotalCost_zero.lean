-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_zero
-- name    : QEC.Coding.BDL26ReplacementMaterialization.extendedTotalCost_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:12:34.565603+00:00
-- url     : https://prove2.me/theorems/169941ac-3907-4300-9d4d-4e385e751db4
-- title:
--   BDL26 Replacement Materialization: extended Total Cost zero
-- statement:
--   The BDL26 Replacement Materialization construction uses the extended Total Cost zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L786-L788
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L786-L788

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

theorem QEC.Coding.BDL26ReplacementMaterialization.extendedTotalCost_zero {L : ℝ} (p : GeometricParameters L)
    (z : Experiment p 0) : extendedTotalCost p 0 z = 0 := by sorry
