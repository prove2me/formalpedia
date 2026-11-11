-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_seed_qz_literal
-- name    : QEC.Coding.BDL26NativePresentationGenerator.seed_qz_literal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T00:45:27.447133+00:00
-- url     : https://prove2.me/theorems/5a82d872-7fe9-4ff0-a1c1-64e8b4e31e4d
-- title:
--   BDL26 Native Presentation Generator: seed qz literal
-- statement:
--   The BDL26 Native Presentation Generator construction uses the seed qz literal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L1104-L1106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L1104-L1106

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

theorem QEC.Coding.BDL26NativePresentationGenerator.seed_qz_literal (q : Fin 5) (z : Fin 2) :
    (qzQ seedFrame q.val z.val).1=baseTannerSquarePresentation.qz q z := by sorry
