-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_rangeQ_cost_le
-- name    : QEC.Coding.BDL26NativePresentationGenerator.rangeQ_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:45:38.799866+00:00
-- url     : https://prove2.me/theorems/40937d23-ceee-42de-bc72-aed5130f2022
-- title:
--   BDL26 Native Presentation Generator: range Q cost le
-- statement:
--   The BDL26 Native Presentation Generator construction uses the range Q cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L109-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L109-L114

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

theorem QEC.Coding.BDL26NativePresentationGenerator.rangeQ_cost_le (n : ℕ) : (rangeQ n).2 ≤ 4*(n+1)^2 := by sorry
