-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PaidRowsComposition_paidHistory_prefix
-- name    : QEC.Coding.BDL26PaidRowsComposition.paidHistory_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T07:37:26.251884+00:00
-- url     : https://prove2.me/theorems/950b06a1-a8d4-447e-847f-2e09660cf8d2
-- title:
--   BDL26 Paid Rows Composition: paid History prefix
-- statement:
--   The BDL26 Paid Rows Composition construction uses the paid History prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L561-L566
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/PaidRowsComposition.lean#L561-L566

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

theorem QEC.Coding.BDL26PaidRowsComposition.paidHistory_prefix {L : ℝ} (p : GeometricParameters L) {M N : ℕ} (h : M ≤ N)
    (z : Experiment p N) (i : Fin (M+1)) :
    paidHistory p M (experimentPrefix p M N h z) i =
      paidHistory p N z (i.castLE (by omega)) := by sorry
