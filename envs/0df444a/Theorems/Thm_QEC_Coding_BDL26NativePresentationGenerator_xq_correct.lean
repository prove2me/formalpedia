-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_xq_correct
-- name    : QEC.Coding.BDL26NativePresentationGenerator.xq_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:43:00.781358+00:00
-- url     : https://prove2.me/theorems/1542492b-ea9c-4653-95d1-f13f6135afb1
-- title:
--   BDL26 Native Presentation Generator: xq correct
-- statement:
--   Complete Boolean X-Q incidence, not merely an equal unlabelled graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3134-L3138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L3134-L3138

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

theorem QEC.Coding.BDL26NativePresentationGenerator.xq_correct (S : OddScale) (n : ℕ) (x : (state S n).presentation.X)
    (q : (state S n).presentation.Q) :
    (xqQ (generateQ S n).1 ((generatedRefines S n).xIndex x).val
      ((generatedRefines S n).qIndex q).val).1=(state S n).presentation.xq x q := by sorry
