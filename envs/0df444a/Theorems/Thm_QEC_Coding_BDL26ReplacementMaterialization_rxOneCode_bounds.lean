-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_rxOneCode_bounds
-- name    : QEC.Coding.BDL26ReplacementMaterialization.rxOneCode_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:40:15.582588+00:00
-- url     : https://prove2.me/theorems/d610582a-1465-4754-a69a-2c8dee936c6f
-- title:
--   BDL26 Replacement Materialization: rx One Code bounds
-- statement:
--   The BDL26 Replacement Materialization construction uses the rx One Code bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L306-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L306-L313

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

theorem QEC.Coding.BDL26ReplacementMaterialization.rxOneCode_bounds (P : TannerSquarePresentation) (S : OddScale) (v : RX1 P S) :
    (rxOneCode P S v).reads ≤ 8 ∧ (rxOneCode P S v).work ≤ 1024 := by sorry
