-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_comp
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:00:40.376218+00:00
-- url     : https://prove2.me/theorems/72748f1a-3c97-4048-92e0-3a84e2b0270e
-- title:
--   BDL26 Finite Embedding Experiment: prefix comp
-- statement:
--   Prefix composition is a pointwise identity, without an almost-everywhere restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L75-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L75-L92

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.prefix_comp {L : ℝ} (p : GeometricParameters L) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (z : Experiment p n) :
    experimentPrefix p l m hlm (experimentPrefix p m n hmn z) = experimentPrefix p l n (hlm.trans hmn) z := by sorry
