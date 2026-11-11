-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_run_cost_le
-- name    : QEC.Coding.BDL26ReplacementMaterialization.PointCode.run_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:37:14.598382+00:00
-- url     : https://prove2.me/theorems/3c6a33af-f207-475d-852d-128d8df5340b
-- title:
--   Point Code: run cost le
-- statement:
--   The Point Code construction uses the run cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L129-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L129-L146

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealExpr_run_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealTest_run_cost_le

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
open QEC.Coding.BDL26ReplacementMaterialization.PointCode
variable {A B : Type*}

theorem QEC.Coding.BDL26ReplacementMaterialization.PointCode.run_cost_le [DecidableEq A] (R : List (A × Space)) (c : PointCode A) :
    (c.run R).2 ≤ 2*R.length*c.reads+c.work := by sorry
