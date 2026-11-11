-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_mapQ_cost
-- name    : QEC.Coding.BDL26NativePresentationGenerator.mapQ_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:42:30.088207+00:00
-- url     : https://prove2.me/theorems/32585dee-b8e6-4917-a9f5-2a9713263fa2
-- title:
--   BDL26 Native Presentation Generator: map Q cost
-- statement:
--   The BDL26 Native Presentation Generator construction uses the map Q cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L71-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L71-L75

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Theorems.Thm_QEC_Semantics_CompletelyPositive_sum
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation

theorem QEC.Coding.BDL26NativePresentationGenerator.mapQ_cost {A B : Type*} (f : A → Query B) (as : List A) :
    (mapQ f as).2 = (as.map (fun a => (f a).2)).sum+as.length := by sorry
