-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_extendedTotalCost_succ
-- name    : QEC.Coding.BDL26ReplacementMaterialization.extendedTotalCost_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:53:42.754738+00:00
-- url     : https://prove2.me/theorems/61bd3f3c-149a-4b79-a820-24c58db49cb1
-- title:
--   BDL26 Replacement Materialization: extended Total Cost succ
-- statement:
--   The BDL26 Replacement Materialization construction uses the extended Total Cost succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L790-L796
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L790-L796

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators

theorem QEC.Coding.BDL26ReplacementMaterialization.extendedTotalCost_succ {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p (N+1)) : extendedTotalCost p (N+1) z = extendedTotalCost p N z.1 +
      (paidSuccessorQuery p N (evaluate p N z.1) z.2).2 := by sorry
