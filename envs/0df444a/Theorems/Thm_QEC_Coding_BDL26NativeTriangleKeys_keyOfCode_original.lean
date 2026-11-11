-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_original
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:53:28.056235+00:00
-- url     : https://prove2.me/theorems/44cdbf5b-f655-4dec-8804-218929dc2f0e
-- title:
--   BDL26 Native Triangle Keys: key Of Code original
-- statement:
--   The BDL26 Native Triangle Keys construction uses the key Of Code original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L373-L376
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L373-L376

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_original (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (keyOfCodeQ S n (encode S n t)).1=some (nativeTriangleIndex S n t).val := by sorry
