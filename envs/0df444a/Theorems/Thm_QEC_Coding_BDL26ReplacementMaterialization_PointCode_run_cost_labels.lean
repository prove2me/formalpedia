-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_run_cost_labels
-- name    : QEC.Coding.BDL26ReplacementMaterialization.PointCode.run_cost_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:09:44.254469+00:00
-- url     : https://prove2.me/theorems/7f2a1417-667f-42a7-bb71-442360532de3
-- title:
--   Point Code: run cost labels
-- statement:
--   The Point Code construction uses the run cost labels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L156-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L156-L159

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
open QEC.Coding.BDL26ReplacementMaterialization.PointCode
variable {A B : Type*}

theorem QEC.Coding.BDL26ReplacementMaterialization.PointCode.run_cost_labels [DecidableEq A] (R : List (A × Space)) (c : PointCode A) :
    (c.run R).2 = c.costOnLabels (R.map Prod.fst) := by sorry
