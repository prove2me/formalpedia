-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamStageCost_finite_prefix
-- name    : QEC.Coding.BDL26PaidRowsComposition.streamStageCost_finite_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:35:20.233224+00:00
-- url     : https://prove2.me/theorems/8b594b0b-d4d1-443e-abdb-7a8771c71f9f
-- title:
--   BDL26 Paid Rows Composition: stream Stage Cost finite prefix
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stream Stage Cost finite prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L597-L602
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L597-L602

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

theorem QEC.Coding.BDL26PaidRowsComposition.streamStageCost_finite_prefix {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamStageCost p i.val omega = stageCost p N i (BDL26CountableEmbeddingExperiment.truncate p N omega) := by sorry
