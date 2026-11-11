-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_qz_correct
-- name    : QEC.Coding.BDL26NativePresentationGenerator.qz_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:44:15.185474+00:00
-- url     : https://prove2.me/theorems/03108a5b-922a-4b90-8630-60bc158a6b47
-- title:
--   BDL26 Native Presentation Generator: qz correct
-- statement:
--   Complete Boolean Q-Z incidence with the same original labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3141-L3145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3141-L3145

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

theorem QEC.Coding.BDL26NativePresentationGenerator.qz_correct (S : OddScale) (n : ℕ) (q : (state S n).presentation.Q)
    (z : (state S n).presentation.Z) :
    (qzQ (generateQ S n).1 ((generatedRefines S n).qIndex q).val
      ((generatedRefines S n).zIndex z).val).1=(state S n).presentation.qz q z := by sorry
