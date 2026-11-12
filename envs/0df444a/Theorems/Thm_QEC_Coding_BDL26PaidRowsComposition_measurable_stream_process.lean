-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_measurable_stream_process
-- name    : QEC.Coding.BDL26PaidRowsComposition.measurable_stream_process
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:39:58.52167+00:00
-- url     : https://prove2.me/theorems/ad6bb3a9-ced3-4a3e-bd02-eab4548e02ec
-- title:
--   BDL26 Paid Rows Composition: measurable stream process
-- statement:
--   The BDL26 Paid Rows Composition construction uses the measurable stream process property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L749-L755
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L749-L755

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

theorem QEC.Coding.BDL26PaidRowsComposition.measurable_stream_process {L : ℝ} (p : GeometricParameters L) :
    Measurable (fun omega : BDL26CountableEmbeddingExperiment.Omega p =>
      (fun n => streamStageTrace p n omega,fun n => streamStageCost p n omega,
       fun N => streamTotalCost p N omega)) := by sorry
