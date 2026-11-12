-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_streamStageCost_prefix
-- name    : QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:23:54.64918+00:00
-- url     : https://prove2.me/theorems/3fbaf57c-7e78-437f-89ce-10607db9cfcb
-- title:
--   BDL26 Countable Embedding Experiment: stream Stage Cost prefix
-- statement:
--   Exact prefix and proof transports, retaining the original stage occurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L75-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/CountableExperimentCost.lean#L75-L80

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ}
    (h : M ≤ N) (i : Fin M) (omega : Omega p) :
    stageCost p M i (experimentPrefix p M N h (truncate p N omega)) =
      streamStageCost p (i.castLE h).val omega := by sorry
