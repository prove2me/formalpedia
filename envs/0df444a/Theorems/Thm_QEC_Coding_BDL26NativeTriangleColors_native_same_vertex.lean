-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_native_same_vertex
-- name    : QEC.Coding.BDL26NativeTriangleColors.native_same_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:27:54.191421+00:00
-- url     : https://prove2.me/theorems/4856f833-cfd9-46f7-a2b3-1854dc9bf9b6
-- title:
--   BDL26 Native Triangle Colors: native same vertex
-- statement:
--   The BDL26 Native Triangle Colors construction uses the native same vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L408-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L408-L411

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

theorem QEC.Coding.BDL26NativeTriangleColors.native_same_vertex (S : OddScale) (n : ℕ) {a b : Triangle (P S n)}
    (hc : nativeColor S n a=nativeColor S n b) {i j : Fin 3}
    (hv : triangleVertex (P S n) a i=triangleVertex (P S n) b j) : a=b := by sorry
