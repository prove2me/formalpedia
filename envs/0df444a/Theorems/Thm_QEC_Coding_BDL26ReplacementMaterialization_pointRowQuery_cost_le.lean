-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_pointRowQuery_cost_le
-- name    : QEC.Coding.BDL26ReplacementMaterialization.pointRowQuery_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:11:37.150381+00:00
-- url     : https://prove2.me/theorems/8c4e5025-dc6c-4040-865b-439c1fbdc9f7
-- title:
--   BDL26 Replacement Materialization: point Row Query cost le
-- statement:
--   The BDL26 Replacement Materialization construction uses the point Row Query cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L41-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L41-L45

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

theorem QEC.Coding.BDL26ReplacementMaterialization.pointRowQuery_cost_le {A : Type*} [DecidableEq A] (v : A)
    (R : List (A × Space)) : (pointRowQuery v R).2 ≤ 2*R.length := by sorry
