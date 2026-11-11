-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_finite_iff
-- name    : QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_finite_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:39:01.321543+00:00
-- url     : https://prove2.me/theorems/faecea27-e34e-426b-a4ee-02b23b16cb00
-- title:
--   BDL26 Paid Rows Composition: stream Total Cost finite iff
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stream Total Cost finite iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L786-L791
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L786-L791

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

theorem QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_finite_iff {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) :
    streamTotalCost p N omega < ∞ ↔
      ∀ i : Fin N, BDL26CountableEmbeddingExperiment.streamHalts p i.val omega := by sorry
