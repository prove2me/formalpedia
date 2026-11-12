-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_seed_xq_literal
-- name    : QEC.Coding.BDL26NativePresentationGenerator.seed_xq_literal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:44:36.902202+00:00
-- url     : https://prove2.me/theorems/f552c7ac-994b-488a-b9c3-06695c7ab073
-- title:
--   BDL26 Native Presentation Generator: seed xq literal
-- statement:
--   The BDL26 Native Presentation Generator construction uses the seed xq literal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L1100-L1102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L1100-L1102

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

theorem QEC.Coding.BDL26NativePresentationGenerator.seed_xq_literal (x : Fin 2) (q : Fin 5) :
    (xqQ seedFrame x.val q.val).1=baseTannerSquarePresentation.xq x q := by sorry
