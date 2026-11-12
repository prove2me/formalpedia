-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_rxTwoCode_bounds
-- name    : QEC.Coding.BDL26ReplacementMaterialization.rxTwoCode_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:41:33.712912+00:00
-- url     : https://prove2.me/theorems/a4202a25-f204-4d40-90fd-3935e75a4e5f
-- title:
--   BDL26 Replacement Materialization: rx Two Code bounds
-- statement:
--   The BDL26 Replacement Materialization construction uses the rx Two Code bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L315-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L315-L327

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

theorem QEC.Coding.BDL26ReplacementMaterialization.rxTwoCode_bounds (P : TannerSquarePresentation) (S : OddScale) (v : RX2 P S) :
    (rxTwoCode P S v).reads ≤ 8 ∧ (rxTwoCode P S v).work ≤ 1024 := by sorry
