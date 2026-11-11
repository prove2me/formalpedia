-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_injective
-- name    : QEC.Coding.BDL26NativeTriangleKeys.encode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:48:40.451053+00:00
-- url     : https://prove2.me/theorems/9ef3cbda-fb75-45a4-80e2-efa603b03fc5
-- title:
--   BDL26 Native Triangle Keys: encode injective
-- statement:
--   The BDL26 Native Triangle Keys construction uses the encode injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L319-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L319-L320

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.encode_injective (S : OddScale) (n : ℕ) : Function.Injective (encode S n) := by sorry
