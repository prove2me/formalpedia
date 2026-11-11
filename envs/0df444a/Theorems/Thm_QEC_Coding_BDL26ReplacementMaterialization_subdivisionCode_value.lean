-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_subdivisionCode_value
-- name    : QEC.Coding.BDL26ReplacementMaterialization.subdivisionCode_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:13:20.053485+00:00
-- url     : https://prove2.me/theorems/6dcbc5fd-2f73-4274-8a64-5c0066e4e5b1
-- title:
--   BDL26 Replacement Materialization: subdivision Code value
-- statement:
--   The BDL26 Replacement Materialization construction uses the subdivision Code value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L224-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L224-L230

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

theorem QEC.Coding.BDL26ReplacementMaterialization.subdivisionCode_value (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → Space) (x : P.X) (v : SubdivisionVertex P x S) :
    (subdivisionCode P S x v).eval J = subdivisionVertexPoint P S J x v := by sorry
