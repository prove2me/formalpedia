-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_finiteObservation_original
-- name    : QEC.Coding.BDL26PaidRowsComposition.finiteObservation_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:34:41.940259+00:00
-- url     : https://prove2.me/theorems/e3cacf19-abbc-456a-a8f3-4db07552ba34
-- title:
--   BDL26 Paid Rows Composition: finite Observation original
-- statement:
--   The BDL26 Paid Rows Composition construction uses the finite Observation original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L528-L530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L528-L530

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

theorem QEC.Coding.BDL26PaidRowsComposition.finiteObservation_original {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    finiteObservation p N z = originalObservation p N z := by sorry
