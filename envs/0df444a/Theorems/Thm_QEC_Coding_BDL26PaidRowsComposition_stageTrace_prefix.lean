-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stageTrace_prefix
-- name    : QEC.Coding.BDL26PaidRowsComposition.stageTrace_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:36:02.634124+00:00
-- url     : https://prove2.me/theorems/bac3432b-a484-45cf-856f-9747c0184056
-- title:
--   BDL26 Paid Rows Composition: stage Trace prefix
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stage Trace prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L541-L559
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L541-L559

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PaidRowsComposition
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26ReplacementMaterialization BDL26IncomingRowsExecution
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26PaidRowsComposition.stageTrace_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ} (h : M ≤ N)
    (i : Fin M) (z : Experiment p N) :
    stageTrace p M i (experimentPrefix p M N h z) = stageTrace p N (i.castLE h) z := by sorry
