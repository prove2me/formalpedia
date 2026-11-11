-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_seed_codes
-- name    : QEC.Coding.BDL26NativeTriangleKeys.seed_codes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:15:44.416435+00:00
-- url     : https://prove2.me/theorems/683a8129-5d86-489e-83da-0f5f470415e7
-- title:
--   BDL26 Native Triangle Keys: seed codes
-- statement:
--   The BDL26 Native Triangle Keys construction uses the seed codes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L251-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L251-L255

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.seed_codes (S : OddScale) :
    (BDL26NativePresentationGenerator.setupQ S 0).1.triangles=frameCodes 4 := by sorry
