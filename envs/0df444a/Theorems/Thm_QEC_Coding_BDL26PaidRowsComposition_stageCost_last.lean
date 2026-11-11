-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stageCost_last
-- name    : QEC.Coding.BDL26PaidRowsComposition.stageCost_last
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:33:08.089219+00:00
-- url     : https://prove2.me/theorems/cf050ca8-8686-442f-9410-94ffd88dfeeb
-- title:
--   BDL26 Paid Rows Composition: stage Cost last
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stage Cost last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L190-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L190-L193

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingRowsExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageCost_last

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

theorem QEC.Coding.BDL26PaidRowsComposition.stageCost_last {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p (N+1)) :
    stageCost p (N+1) (Fin.last N) z =
      (composedStageQuery p N (run p N z.1).1 z.2).2 := by sorry
