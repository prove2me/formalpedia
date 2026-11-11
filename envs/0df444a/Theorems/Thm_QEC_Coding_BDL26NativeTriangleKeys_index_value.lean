-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_index_value
-- name    : QEC.Coding.BDL26NativeTriangleKeys.index_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T00:17:22.97821+00:00
-- url     : https://prove2.me/theorems/29f4c79e-3286-4329-acd3-5f2c421ed942
-- title:
--   BDL26 Native Triangle Keys: index value
-- statement:
--   The BDL26 Native Triangle Keys construction uses the index value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L301-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L301-L303

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.index_value (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (nativeTriangleIndex S n t).val=
      2*((BDL26NativePresentationGenerator.generatedRefines S n).fIndex t.1).val+t.2.val := by sorry
