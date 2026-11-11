-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_readback
-- name    : QEC.Coding.BDL26NativeTriangleKeys.encode_readback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:55:57.266617+00:00
-- url     : https://prove2.me/theorems/78bed5e0-d45e-4c25-9503-a7fa48f618c0
-- title:
--   BDL26 Native Triangle Keys: encode readback
-- statement:
--   The BDL26 Native Triangle Keys construction uses the encode readback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L322-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L322-L327

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.encode_readback (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    codeAtKey (nativeTriangleIndex S n t).val=encode S n t := by sorry
