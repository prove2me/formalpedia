-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_actualStage_nonhalting_default
-- name    : QEC.Coding.BDL26PaidRowsComposition.actualStage_nonhalting_default
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:35:49.052272+00:00
-- url     : https://prove2.me/theorems/9fb8de8b-7a32-4ae3-97db-d7d1c3f221de
-- title:
--   BDL26 Paid Rows Composition: actual Stage nonhalting default
-- statement:
--   Original exceptional defaults and infinite paid cost concern the very same table.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L447-L455
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L447-L455

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

theorem QEC.Coding.BDL26PaidRowsComposition.actualStage_nonhalting_default {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (z : Experiment p N) (h : ¬actualStageHalts p N i z) :
    actualStageHaltTime p N i z = 0 ∧
      actualStageGeometric p N i z = assignment (tableAt p N i z) (fun _ => 0) ∧
      stageCost p N i z = ∞ := by sorry
