-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_allFiniteSuccess_paid
-- name    : QEC.Coding.BDL26PaidRowsComposition.allFiniteSuccess_paid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:04:20.21068+00:00
-- url     : https://prove2.me/theorems/aa7dc74a-fd32-43fc-8fcc-7ba5c86adaef
-- title:
--   BDL26 Paid Rows Composition: all Finite Success paid
-- statement:
--   The BDL26 Paid Rows Composition construction uses the all Finite Success paid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L793-L803
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L793-L803

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

theorem QEC.Coding.BDL26PaidRowsComposition.allFiniteSuccess_paid {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) :
    (∀ N, streamTotalCost p N omega < ∞) ∧
      (∀ n, PhysicalSuccessorFacts p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)) ∧
      ∀ n, PhysicalGeometry (perturbationOddScale p) n
        (BDL26CountableEmbeddingExperiment.levelMap p omega n) p.t := by sorry
