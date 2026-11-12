-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_native_support_disjoint
-- name    : QEC.Coding.BDL26NativeTriangleColors.native_support_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:27:36.881478+00:00
-- url     : https://prove2.me/theorems/5a15d694-dc6b-49e6-925d-270dbfb89e6d
-- title:
--   BDL26 Native Triangle Colors: native support disjoint
-- statement:
--   The BDL26 Native Triangle Colors construction uses the native support disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L413-L416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L413-L416

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

theorem QEC.Coding.BDL26NativeTriangleColors.native_support_disjoint (S : OddScale) (n : ℕ) {a b : Triangle (P S n)}
    (hne : a≠b) (hc : nativeColor S n a=nativeColor S n b) :
    Disjoint (triangleSupport (P S n) a) (triangleSupport (P S n) b) := by sorry
