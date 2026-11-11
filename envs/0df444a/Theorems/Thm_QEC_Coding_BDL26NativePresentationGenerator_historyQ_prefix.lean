-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_historyQ_prefix
-- name    : QEC.Coding.BDL26NativePresentationGenerator.historyQ_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:42:17.10785+00:00
-- url     : https://prove2.me/theorems/7905c606-f929-475e-add3-8d0d3d3d5dd4
-- title:
--   BDL26 Native Presentation Generator: history Q prefix
-- statement:
--   The BDL26 Native Presentation Generator construction uses the history Q prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L750-L753
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L750-L753

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

theorem QEC.Coding.BDL26NativePresentationGenerator.historyQ_prefix (S : OddScale) (n : ℕ) :
    ((historyQ S (n+1)).1).take (n+1)=(historyQ S n).1 := by sorry
