-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_composedStageQuery_rows
-- name    : QEC.Coding.BDL26PaidRowsComposition.composedStageQuery_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:55:55.046205+00:00
-- url     : https://prove2.me/theorems/b05a213b-179d-48b8-acd5-e4aa6e139a35
-- title:
--   BDL26 Paid Rows Composition: composed Stage Query rows
-- statement:
--   The BDL26 Paid Rows Composition construction uses the composed Stage Query rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L85-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L85-L90

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

theorem QEC.Coding.BDL26PaidRowsComposition.composedStageQuery_rows {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (composedStageQuery p n (incomingRows (StagePresentation p n) J) T).1 =
      incomingRows (StagePresentation p (n+1)) (physicalSuccessorOutput p n J T) := by sorry
