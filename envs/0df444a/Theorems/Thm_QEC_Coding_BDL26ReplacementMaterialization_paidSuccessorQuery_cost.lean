-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_paidSuccessorQuery_cost
-- name    : QEC.Coding.BDL26ReplacementMaterialization.paidSuccessorQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:45:00.543306+00:00
-- url     : https://prove2.me/theorems/0bb6b41c-ceda-4549-a9c5-e08d283c1217
-- title:
--   BDL26 Replacement Materialization: paid Successor Query cost
-- statement:
--   The BDL26 Replacement Materialization construction uses the paid Successor Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L561-L565
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L561-L565

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

theorem QEC.Coding.BDL26ReplacementMaterialization.paidSuccessorQuery_cost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : StageTables p n) :
    (paidSuccessorQuery p n J T).2 = jointStageCost p n (J,T) + (materializationCost p n (J,T) : ℕ) := by sorry
