-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_perturbationEmbeddingOutput
-- name    : QEC.Coding.BDL26RandomPerturbation.measurable_perturbationEmbeddingOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:30:07.697443+00:00
-- url     : https://prove2.me/theorems/acf48c30-fde3-46ed-b2f8-a60d23407e4c
-- title:
--   BDL26 Random Perturbation: measurable perturbation Embedding Output
-- statement:
--   The BDL26 Random Perturbation construction uses the measurable perturbation Embedding Output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L65-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/RandomizedEmbeddingStep.lean#L65-L69

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal

theorem QEC.Coding.BDL26RandomPerturbation.measurable_perturbationEmbeddingOutput (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) : Measurable (perturbationEmbeddingOutput P J p) := by sorry
