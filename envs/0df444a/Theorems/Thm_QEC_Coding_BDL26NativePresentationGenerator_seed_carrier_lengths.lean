-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_seed_carrier_lengths
-- name    : QEC.Coding.BDL26NativePresentationGenerator.seed_carrier_lengths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:41:48.750946+00:00
-- url     : https://prove2.me/theorems/b39d7fec-f923-427d-908a-839c7da1f0a0
-- title:
--   BDL26 Native Presentation Generator: seed carrier lengths
-- statement:
--   The BDL26 Native Presentation Generator construction uses the seed carrier lengths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L264-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NativePresentationGenerator.lean#L264-L266

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

theorem QEC.Coding.BDL26NativePresentationGenerator.seed_carrier_lengths :
    seedFrame.xs.length=2 ∧ seedFrame.qs.length=5 ∧ seedFrame.zs.length=2 ∧
      seedFrame.faces.length=4 := by sorry
