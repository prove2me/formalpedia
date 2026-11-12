-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_native_bounded_value
-- name    : QEC.Coding.BDL26NativeTriangleColors.native_bounded_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:26:39.498116+00:00
-- url     : https://prove2.me/theorems/755d5f56-08dc-493c-95a8-098c2f1360e7
-- title:
--   BDL26 Native Triangle Colors: native bounded value
-- statement:
--   The BDL26 Native Triangle Colors construction uses the native bounded value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L394-L395
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L394-L395

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeTriangleColors.native_bounded_value (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    (nativeBoundedColor S n t i).val=nativeColor S n t i := by sorry
