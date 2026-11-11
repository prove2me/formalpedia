-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_triangle_readback
-- name    : QEC.Coding.BDL26NativeTriangleKeys.triangle_readback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:15:34.809815+00:00
-- url     : https://prove2.me/theorems/44202d91-5612-401d-ad1b-5868a292bc29
-- title:
--   BDL26 Native Triangle Keys: triangle readback
-- statement:
--   The BDL26 Native Triangle Keys construction uses the triangle readback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L329-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L329-L342

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.triangle_readback (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (BDL26NativePresentationGenerator.setupQ S n).1.triangles[(nativeTriangleIndex S n t).val]?=
      some (encode S n t) := by sorry
