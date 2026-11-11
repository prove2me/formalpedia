-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_last
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:24:49.522767+00:00
-- url     : https://prove2.me/theorems/f58a3728-049a-41c6-8845-334e62af57cc
-- title:
--   BDL26 Finite Embedding Experiment: stage Cost last
-- statement:
--   The final stage reads precisely the preceding output and the last original factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L70-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperimentCost.lean#L70-L74

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_last {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (z : Experiment p (n+1)) :
    stageCost p (n+1) (Fin.last n) z =
      jointStageCost p n (evaluate p n z.1, z.2) := by sorry
