-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_starCode_bounds
-- name    : QEC.Coding.BDL26ReplacementMaterialization.starCode_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:11:06.867546+00:00
-- url     : https://prove2.me/theorems/e4e7385e-7947-4a42-9ae4-1f4cf592511d
-- title:
--   BDL26 Replacement Materialization: star Code bounds
-- statement:
--   The BDL26 Replacement Materialization construction uses the star Code bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L211-L214
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L211-L214

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

theorem QEC.Coding.BDL26ReplacementMaterialization.starCode_bounds (P : TannerSquarePresentation) (S : OddScale)
    (x : P.X) (v : XStarVertex P x) :
    (starCode P S x v).reads ≤ 2 ∧ (starCode P S x v).work ≤ 40 := by sorry
