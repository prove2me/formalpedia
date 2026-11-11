-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_run_value
-- name    : QEC.Coding.BDL26ReplacementMaterialization.PointCode.run_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:35:46.547194+00:00
-- url     : https://prove2.me/theorems/0bfaa1f1-c9e8-4926-a0fb-8cf1d0dec8fc
-- title:
--   Point Code: run value
-- statement:
--   The Point Code construction uses the run value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L119-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L119-L127

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealExpr_run_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealTest_run_value

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

theorem QEC.Coding.BDL26ReplacementMaterialization.PointCode.run_value [DecidableEq A] (J : A → Space) (L : List A)
    (hL : ∀ v, v ∈ L) (c : PointCode A) :
    (c.run (L.map (fun v => (v,J v)))).1 = c.eval J := by sorry
