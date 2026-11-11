-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_pointRowQuery_map
-- name    : QEC.Coding.BDL26ReplacementMaterialization.pointRowQuery_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:09:59.541199+00:00
-- url     : https://prove2.me/theorems/20c15d82-5ac5-4b7a-9590-a6409a7a039d
-- title:
--   BDL26 Replacement Materialization: point Row Query map
-- statement:
--   The BDL26 Replacement Materialization construction uses the point Row Query map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L47-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L47-L57

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

theorem QEC.Coding.BDL26ReplacementMaterialization.pointRowQuery_map {A : Type*} [DecidableEq A] (J : A → Space)
    (v : A) (L : List A) (h : v ∈ L) :
    (pointRowQuery v (L.map (fun a => (a,J a)))).1 = J v := by sorry
