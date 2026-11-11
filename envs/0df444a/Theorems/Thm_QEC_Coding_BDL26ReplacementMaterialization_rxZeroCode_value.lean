-- Prove2me | Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_rxZeroCode_value
-- name    : QEC.Coding.BDL26ReplacementMaterialization.rxZeroCode_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T03:39:02.518616+00:00
-- url     : https://prove2.me/theorems/12eb6eba-c7d2-4be9-abbd-d743194d5477
-- title:
--   BDL26 Replacement Materialization: rx Zero Code value
-- statement:
--   The BDL26 Replacement Materialization construction uses the rx Zero Code value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L285-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ReplacementMaterialization.lean#L285-L287

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

theorem QEC.Coding.BDL26ReplacementMaterialization.rxZeroCode_value (P : TannerSquarePresentation) (S : OddScale) (J : Vertex P → Space)
    (v : RX0 P S) : (rxZeroCode P S v).eval J = rxZeroPoint P S J v := by sorry
