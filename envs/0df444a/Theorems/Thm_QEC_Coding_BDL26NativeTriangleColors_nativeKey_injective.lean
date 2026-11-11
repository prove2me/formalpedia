-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
-- name    : QEC.Coding.BDL26NativeTriangleColors.nativeKey_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:26:17.730702+00:00
-- url     : https://prove2.me/theorems/bb39675a-8c6d-4c59-a778-5015c515445a
-- title:
--   BDL26 Native Triangle Colors: native Key injective
-- statement:
--   The BDL26 Native Triangle Colors construction uses the native Key injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L377-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L377-L379

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

theorem QEC.Coding.BDL26NativeTriangleColors.nativeKey_injective (S : OddScale) (n : ℕ) : Function.Injective (nativeKey S n) := by sorry
