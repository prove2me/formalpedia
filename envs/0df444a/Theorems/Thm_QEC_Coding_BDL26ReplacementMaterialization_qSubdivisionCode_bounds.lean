-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_qSubdivisionCode_bounds
-- name    : QEC.Coding.BDL26ReplacementMaterialization.qSubdivisionCode_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:39:17.649667+00:00
-- url     : https://prove2.me/theorems/78b8c4e8-89dd-4197-9d29-074831ab42f2
-- title:
--   BDL26 Replacement Materialization: q Subdivision Code bounds
-- statement:
--   The BDL26 Replacement Materialization construction uses the q Subdivision Code bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L259-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L259-L264

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

theorem QEC.Coding.BDL26ReplacementMaterialization.qSubdivisionCode_bounds (P : TannerSquarePresentation) (S : OddScale)
    (q : P.Q) (v : QSubdivisionVertex P q S) :
    (qSubdivisionCode P S q v).reads ≤ 2 ∧ (qSubdivisionCode P S q v).work ≤ 48 := by sorry
