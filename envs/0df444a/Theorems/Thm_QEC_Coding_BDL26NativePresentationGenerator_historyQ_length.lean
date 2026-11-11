-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_historyQ_length
-- name    : QEC.Coding.BDL26NativePresentationGenerator.historyQ_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:47:33.758194+00:00
-- url     : https://prove2.me/theorems/a1b0555e-9bb6-48a2-808a-5fdc23d45dbf
-- title:
--   BDL26 Native Presentation Generator: history Q length
-- statement:
--   The BDL26 Native Presentation Generator construction uses the history Q length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L745-L748
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L745-L748

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

theorem QEC.Coding.BDL26NativePresentationGenerator.historyQ_length (S : OddScale) (n : ℕ) : (historyQ S n).1.length=n+1 := by sorry
