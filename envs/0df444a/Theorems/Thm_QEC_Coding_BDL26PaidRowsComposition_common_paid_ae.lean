-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_common_paid_ae
-- name    : QEC.Coding.BDL26PaidRowsComposition.common_paid_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:38:38.655432+00:00
-- url     : https://prove2.me/theorems/71cc6425-54c6-4ec8-8411-ed6517e95fb1
-- title:
--   BDL26 Paid Rows Composition: common paid ae
-- statement:
--   The BDL26 Paid Rows Composition construction uses the common paid ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L812-L820
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L812-L820

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

theorem QEC.Coding.BDL26PaidRowsComposition.common_paid_ae {L : ℝ} (p : GeometricParameters L) :
    ∀ᵐ omega ∂BDL26CountableEmbeddingExperiment.streamLaw p,
      omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p ∧
      (∀ N, streamTotalCost p N omega < ∞) ∧
      (∀ n, PhysicalSuccessorFacts p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n
        (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t := by sorry
