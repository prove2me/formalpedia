-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_castSucc
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_castSucc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:29:58.837203+00:00
-- url     : https://prove2.me/theorems/423a06ec-c095-4ae8-93d5-78295e34dffa
-- title:
--   BDL26 Finite Embedding Experiment: stage Cost cast Succ
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the stage Cost cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L76-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L76-L82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_castSucc {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) (z : Experiment p (n+1)) :
    stageCost p (n+1) i.castSucc z = stageCost p n i z.1 := by sorry
