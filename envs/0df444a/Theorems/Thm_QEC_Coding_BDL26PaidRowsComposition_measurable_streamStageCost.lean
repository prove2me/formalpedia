-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_streamStageCost
-- name    : QEC.Coding.BDL26PaidRowsComposition.measurable_streamStageCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:36:29.949301+00:00
-- url     : https://prove2.me/theorems/b3ecc187-5701-4242-bc58-a1941fa02e57
-- title:
--   BDL26 Paid Rows Composition: measurable stream Stage Cost
-- statement:
--   The BDL26 Paid Rows Composition construction uses the measurable stream Stage Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L718-L725
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L718-L725

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_streamStageCost

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

theorem QEC.Coding.BDL26PaidRowsComposition.measurable_streamStageCost {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamStageCost p n) := by sorry
