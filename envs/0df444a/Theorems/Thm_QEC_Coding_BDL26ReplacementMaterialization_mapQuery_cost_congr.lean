-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_mapQuery_cost_congr
-- name    : QEC.Coding.BDL26ReplacementMaterialization.mapQuery_cost_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:11:46.499867+00:00
-- url     : https://prove2.me/theorems/0ecf070d-6f9d-4834-b0eb-c9a6172e8b8f
-- title:
--   BDL26 Replacement Materialization: map Query cost congr
-- statement:
--   The BDL26 Replacement Materialization construction uses the map Query cost congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L501-L505
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L501-L505

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mapQuery_cost_congr

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

theorem QEC.Coding.BDL26ReplacementMaterialization.mapQuery_cost_congr {A B C : Type*} (q : A → B × ℕ) (r : A → C × ℕ)
    (h : ∀ a, (q a).2 = (r a).2) (L : List A) : (mapQuery q L).2 = (mapQuery r L).2 := by sorry
