-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_native_order
-- name    : QEC.Coding.BDL26NativeTriangleKeys.native_order
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:37:58.86911+00:00
-- url     : https://prove2.me/theorems/a3f20ee4-c18e-4775-8802-a935059d09ee
-- title:
--   BDL26 Native Triangle Keys: native order
-- statement:
--   The BDL26 Native Triangle Keys construction uses the native order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L444-L451
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L444-L451

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.native_order (S : OddScale) (n : ℕ) :
    (∀a b,nativeLE S n a b ∨ nativeLE S n b a) ∧
      (∀a b c,nativeLE S n a b → nativeLE S n b c → nativeLE S n a c) ∧
      (∀a b,nativeLE S n a b → nativeLE S n b a → a=b) := by sorry
