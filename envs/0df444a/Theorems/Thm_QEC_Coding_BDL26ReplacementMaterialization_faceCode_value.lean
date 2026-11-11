-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_faceCode_value
-- name    : QEC.Coding.BDL26ReplacementMaterialization.faceCode_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T03:38:37.5562+00:00
-- url     : https://prove2.me/theorems/aebce74f-e941-47b2-84c3-e5c642bafa49
-- title:
--   BDL26 Replacement Materialization: face Code value
-- statement:
--   The BDL26 Replacement Materialization construction uses the face Code value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L190-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L190-L194

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

theorem QEC.Coding.BDL26ReplacementMaterialization.faceCode_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (f : P.Face) (u v : RealExpr) :
    (faceCode P f u v).eval J =
      facePoint P J f (u.eval (fun _ => 0) 0 0) (v.eval (fun _ => 0) 0 0) := by sorry
