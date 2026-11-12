-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_native_chain
-- name    : QEC.Coding.BDL26NativePresentationGenerator.native_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:47:13.224534+00:00
-- url     : https://prove2.me/theorems/73cceb9a-00c5-4072-b88e-a3adf8617700
-- title:
--   BDL26 Native Presentation Generator: native chain
-- statement:
--   The complete pairing identity is transported by the constructed Q bijection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3155-L3177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3155-L3177

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

theorem QEC.Coding.BDL26NativePresentationGenerator.native_chain (S : OddScale) (n : ℕ) :
    nativeXQ (generateQ S n).1 * nativeQZ (generateQ S n).1=0 := by sorry
