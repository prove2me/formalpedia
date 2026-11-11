-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_dedupQ_length_le
-- name    : QEC.Coding.BDL26NativePresentationGenerator.dedupQ_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:43:35.034202+00:00
-- url     : https://prove2.me/theorems/13768ca6-13e7-4e59-9fab-5b56b34b7703
-- title:
--   BDL26 Native Presentation Generator: dedup Q length le
-- statement:
--   The BDL26 Native Presentation Generator construction uses the dedup Q length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L681-L688
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L681-L688

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

theorem QEC.Coding.BDL26NativePresentationGenerator.dedupQ_length_le (as : List Code) : (dedupQ as).1.length≤ as.length := by sorry
