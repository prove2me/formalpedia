-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_member
-- name    : QEC.Coding.BDL26NativeTriangleKeys.encode_member
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:48:00.882383+00:00
-- url     : https://prove2.me/theorems/80152f84-1797-442d-bf76-c875b154466b
-- title:
--   BDL26 Native Triangle Keys: encode member
-- statement:
--   The BDL26 Native Triangle Keys construction uses the encode member property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L315-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L315-L317

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.encode_member (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    encode S n t∈(BDL26NativePresentationGenerator.setupQ S n).1.triangles := by sorry
