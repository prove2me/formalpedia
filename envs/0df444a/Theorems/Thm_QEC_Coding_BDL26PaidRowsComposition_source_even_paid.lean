-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_source_even_paid
-- name    : QEC.Coding.BDL26PaidRowsComposition.source_even_paid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:41:35.4418+00:00
-- url     : https://prove2.me/theorems/5ce2624d-4930-4f93-a873-294b7271ee80
-- title:
--   BDL26 Paid Rows Composition: source even paid
-- statement:
--   The BDL26 Paid Rows Composition construction uses the source even paid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L805-L810
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L805-L810

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

theorem QEC.Coding.BDL26PaidRowsComposition.source_even_paid {L : ℝ} (p : GeometricParameters L)
    {omega : BDL26CountableEmbeddingExperiment.Omega p}
    (h : omega ∈ BDL26CountableEmbeddingExperiment.allFiniteSuccess p) (k : ℕ) :
    streamTotalCost p (2*k) omega < ∞ ∧ PhysicalGeometry (perturbationOddScale p) (2*k)
      (BDL26CountableEmbeddingExperiment.levelMap p omega (2*k)) p.t := by sorry
