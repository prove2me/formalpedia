-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_qSubdivisionCode_value
-- name    : QEC.Coding.BDL26ReplacementMaterialization.qSubdivisionCode_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:38:47.737704+00:00
-- url     : https://prove2.me/theorems/e81bcd34-e4af-47ca-aebf-c39033b4b23e
-- title:
--   BDL26 Replacement Materialization: q Subdivision Code value
-- statement:
--   The BDL26 Replacement Materialization construction uses the q Subdivision Code value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L252-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L252-L257

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

theorem QEC.Coding.BDL26ReplacementMaterialization.qSubdivisionCode_value (P : TannerSquarePresentation) (S : OddScale)
    (J : Vertex P → Space) (q : P.Q) (v : QSubdivisionVertex P q S) :
    (qSubdivisionCode P S q v).eval J = qSubdivisionVertexPoint P S J q v := by sorry
