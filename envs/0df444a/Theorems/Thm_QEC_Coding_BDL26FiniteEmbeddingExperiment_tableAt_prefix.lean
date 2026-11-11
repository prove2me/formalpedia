-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_tableAt_prefix
-- name    : QEC.Coding.BDL26FiniteEmbeddingExperiment.tableAt_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T02:03:33.941937+00:00
-- url     : https://prove2.me/theorems/9ea49201-ecea-4288-9a93-57a6e659ac7f
-- title:
--   BDL26 Finite Embedding Experiment: table At prefix
-- statement:
--   The BDL26 Finite Embedding Experiment construction uses the table At prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L109-L113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FiniteExperiment/Core.lean#L109-L113

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

theorem QEC.Coding.BDL26FiniteEmbeddingExperiment.tableAt_prefix {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) (z : Experiment p n) :
    tableAt p m i (experimentPrefix p m n h z) = tableAt p n (i.castLE h) z := by sorry
