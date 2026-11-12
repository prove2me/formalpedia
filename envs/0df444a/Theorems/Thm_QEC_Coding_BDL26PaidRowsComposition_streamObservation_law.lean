-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamObservation_law
-- name    : QEC.Coding.BDL26PaidRowsComposition.streamObservation_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:41:10.126238+00:00
-- url     : https://prove2.me/theorems/2e5ba476-f0f7-428e-911e-f5aa1013a95b
-- title:
--   BDL26 Paid Rows Composition: stream Observation law
-- statement:
--   Complete history/counter/selector/stopped/cost copula, including exceptional inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L758-L766
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L758-L766

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

theorem QEC.Coding.BDL26PaidRowsComposition.streamObservation_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (BDL26CountableEmbeddingExperiment.streamLaw p).map (streamObservation p N) =
      (experimentLaw p N).map (originalObservation p N) := by sorry
