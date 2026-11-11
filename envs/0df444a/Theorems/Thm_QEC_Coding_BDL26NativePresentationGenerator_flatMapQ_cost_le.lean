-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_flatMapQ_cost_le
-- name    : QEC.Coding.BDL26NativePresentationGenerator.flatMapQ_cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:43:43.63849+00:00
-- url     : https://prove2.me/theorems/95902829-8126-4da1-9981-82ebe61557bb
-- title:
--   BDL26 Native Presentation Generator: flat Map Q cost le
-- statement:
--   The BDL26 Native Presentation Generator construction uses the flat Map Q cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L311-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L311-L322

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation

theorem QEC.Coding.BDL26NativePresentationGenerator.flatMapQ_cost_le {A B : Type*} (f : A → Query (List B)) (as : List A)
    (lengthBound costBound : ℕ) (hl : ∀ a∈as,(f a).1.length≤ lengthBound)
    (hc : ∀ a∈as,(f a).2≤ costBound) :
    (flatMapQ f as).2≤ as.length*(lengthBound+costBound+2) := by sorry
