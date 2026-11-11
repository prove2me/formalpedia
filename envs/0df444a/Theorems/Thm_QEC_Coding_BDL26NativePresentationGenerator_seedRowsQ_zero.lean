-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_seedRowsQ_zero
-- name    : QEC.Coding.BDL26NativePresentationGenerator.seedRowsQ_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:59:33.782197+00:00
-- url     : https://prove2.me/theorems/e419a962-7a20-413b-9259-771858e0b179
-- title:
--   BDL26 Native Presentation Generator: seed Rows Q zero
-- statement:
--   The BDL26 Native Presentation Generator construction uses the seed Rows Q zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L869-L872
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L869-L872

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

theorem QEC.Coding.BDL26NativePresentationGenerator.seedRowsQ_zero (r : SeedRow) (hr : r∈seedRowsQ.1) :
    r.counter=0 ∧ r.point=(0,0,0) := by sorry
