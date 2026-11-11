-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_integral_le
-- name    : QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_integral_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:35:45.008632+00:00
-- url     : https://prove2.me/theorems/2e9cc657-6af1-4c65-b5cd-5fda0b3bd7ff
-- title:
--   BDL26 Paid Rows Composition: stream Total Cost integral le
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stream Total Cost integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L779-L784
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L779-L784

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

theorem QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_integral_le {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, streamTotalCost p N omega ∂BDL26CountableEmbeddingExperiment.streamLaw p) ≤
      (((391*operationConstant ((6*p.m+2)*p.lambda)*65^10+65536*65^2+195)*
        (stageQubits p N+1)^12 : ℕ) : ℝ≥0∞) := by sorry
