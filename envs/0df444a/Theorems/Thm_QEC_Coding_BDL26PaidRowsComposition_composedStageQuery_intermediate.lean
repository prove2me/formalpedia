-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_composedStageQuery_intermediate
-- name    : QEC.Coding.BDL26PaidRowsComposition.composedStageQuery_intermediate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:53:59.040956+00:00
-- url     : https://prove2.me/theorems/7ca60017-8452-4f2a-843e-43e0c05ff44f
-- title:
--   BDL26 Paid Rows Composition: composed Stage Query intermediate
-- statement:
--   The BDL26 Paid Rows Composition construction uses the composed Stage Query intermediate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L78-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L78-L83

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

theorem QEC.Coding.BDL26PaidRowsComposition.composedStageQuery_intermediate {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (rowExecutionQuery (StagePresentation p n) (incomingRows (StagePresentation p n) J)
      (by positivity : (0 : ℝ) ≤ anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) T).1 =
      emittedRows p n J T := by sorry
