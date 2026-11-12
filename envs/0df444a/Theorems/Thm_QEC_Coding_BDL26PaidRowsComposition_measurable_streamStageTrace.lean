-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_streamStageTrace
-- name    : QEC.Coding.BDL26PaidRowsComposition.measurable_streamStageTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:36:38.708307+00:00
-- url     : https://prove2.me/theorems/2ce0551f-3019-42cd-b07b-73507d264b31
-- title:
--   BDL26 Paid Rows Composition: measurable stream Stage Trace
-- statement:
--   The BDL26 Paid Rows Composition construction uses the measurable stream Stage Trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L734-L740
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L734-L740

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

theorem QEC.Coding.BDL26PaidRowsComposition.measurable_streamStageTrace {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (streamStageTrace p n) := by sorry
