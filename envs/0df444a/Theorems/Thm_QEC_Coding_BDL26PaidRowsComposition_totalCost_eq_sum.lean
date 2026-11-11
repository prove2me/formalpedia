-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_totalCost_eq_sum
-- name    : QEC.Coding.BDL26PaidRowsComposition.totalCost_eq_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:56:29.847412+00:00
-- url     : https://prove2.me/theorems/b156a1a4-a75a-48b0-afda-e67cc19d19a8
-- title:
--   BDL26 Paid Rows Composition: total Cost eq sum
-- statement:
--   The BDL26 Paid Rows Composition construction uses the total Cost eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L179-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L179-L182

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

theorem QEC.Coding.BDL26PaidRowsComposition.totalCost_eq_sum {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N) :
    totalCost p N z = ∑ i : Fin N, stageCost p N i z := by sorry
