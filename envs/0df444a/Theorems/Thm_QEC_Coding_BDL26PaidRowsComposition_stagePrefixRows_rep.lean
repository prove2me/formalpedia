-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_stagePrefixRows_rep
-- name    : QEC.Coding.BDL26PaidRowsComposition.stagePrefixRows_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:58:02.078172+00:00
-- url     : https://prove2.me/theorems/fc547d93-ca4f-4d42-827f-dd7ffd7b3004
-- title:
--   BDL26 Paid Rows Composition: stage Prefix Rows rep
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stage Prefix Rows rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L293-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L293-L313

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

theorem QEC.Coding.BDL26PaidRowsComposition.stagePrefixRows_rep {L : ℝ} (p : GeometricParameters L) (N : ℕ) (i : Fin N)
    (time : ℕ) (z : Experiment p N) :
    StateRowsRep (StagePresentation p i.val) (tableAt p N i z)
      (stageCounters p N i time z) (stagePrefixRows p N i time z) := by sorry
