-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedStageCost_prefix
-- name    : QEC.Coding.BDL26ReplacementMaterialization.extendedStageCost_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:51:36.896717+00:00
-- url     : https://prove2.me/theorems/08ff362e-f947-438b-91b6-9d17a3c13326
-- title:
--   BDL26 Replacement Materialization: extended Stage Cost prefix
-- statement:
--   The BDL26 Replacement Materialization construction uses the extended Stage Cost prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L781-L784
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L781-L784

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

theorem QEC.Coding.BDL26ReplacementMaterialization.extendedStageCost_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ}
    (h : M ≤ N) (i : Fin M) (z : Experiment p N) :
    extendedStageCost p M i (experimentPrefix p M N h z) = extendedStageCost p N (i.castLE h) z := by sorry
