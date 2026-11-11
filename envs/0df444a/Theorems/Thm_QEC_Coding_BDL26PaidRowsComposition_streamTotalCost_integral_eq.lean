-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_streamTotalCost_integral_eq
-- name    : QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_integral_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:35:27.518641+00:00
-- url     : https://prove2.me/theorems/aefed85d-3932-40e1-a2a4-97a2c5009b29
-- title:
--   BDL26 Paid Rows Composition: stream Total Cost integral eq
-- statement:
--   The BDL26 Paid Rows Composition construction uses the stream Total Cost integral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L768-L777
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L768-L777

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

theorem QEC.Coding.BDL26PaidRowsComposition.streamTotalCost_integral_eq {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (∫⁻ omega, streamTotalCost p N omega ∂BDL26CountableEmbeddingExperiment.streamLaw p) =
      ∫⁻ z, totalCost p N z ∂experimentLaw p N := by sorry
