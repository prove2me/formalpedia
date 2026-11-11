-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_generate_cost
-- name    : QEC.Coding.BDL26NativePresentationGenerator.generate_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:04:55.687805+00:00
-- url     : https://prove2.me/theorems/b52acdae-9b6d-450f-9b47-95114594a982
-- title:
--   BDL26 Native Presentation Generator: generate cost
-- statement:
--   The retained stage prefix is reused and the complete generation cost is polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L4617-L4651
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L4617-L4651

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

theorem QEC.Coding.BDL26NativePresentationGenerator.generate_cost (S : OddScale) (n : ℕ) :
    (generateQ S n).2≤(n+1)*(inputRadius S n)^205 := by sorry
