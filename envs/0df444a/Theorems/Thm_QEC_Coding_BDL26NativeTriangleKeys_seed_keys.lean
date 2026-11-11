-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_seed_keys
-- name    : QEC.Coding.BDL26NativeTriangleKeys.seed_keys
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:33:29.182595+00:00
-- url     : https://prove2.me/theorems/f53b67ff-ad9c-4d2f-bdd3-97dbbfe6a955
-- title:
--   BDL26 Native Triangle Keys: seed keys
-- statement:
--   The BDL26 Native Triangle Keys construction uses the seed keys property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L257-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L257-L260

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.seed_keys (S : OddScale) :
    ((keySetupQ S 0).1.map Prod.snd)=List.range 8 := by sorry
