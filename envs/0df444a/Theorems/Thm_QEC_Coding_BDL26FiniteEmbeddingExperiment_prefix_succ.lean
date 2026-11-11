-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_succ
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:01:13.927201+00:00
-- url     : https://prove2.me/theorems/17c4f10b-cabd-4ae8-8a16-6c1b54894206
-- title:
--   BDL26 Finite Embedding Experiment: prefix succ
-- statement:
--   Deleting a final stage does not inspect its table.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L64-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L64-L68

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_succ {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (z : Experiment p (n+1)) :
    experimentPrefix p m (n+1) (by omega) z = experimentPrefix p m n h z.1 := by sorry
