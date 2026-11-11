-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stage_observation_prefix
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.stage_observation_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:28:57.702343+00:00
-- url     : https://prove2.me/theorems/771fe08f-485b-412f-a26f-50957b8b9460
-- title:
--   BDL26 Finite Embedding Experiment: stage observation prefix
-- statement:
--   Every observation of a retained stage has exactly the same input and table.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L90-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment.lean#L90-L94

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.stage_observation_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) {Y : Type*}
    (F : StageMaps p i.val × StageTables p i.val → Y) (z : Experiment p n) :
    F (stagePair p m i (experimentPrefix p m n h z)) = F (stagePair p n (i.castLE h) z) := by sorry
