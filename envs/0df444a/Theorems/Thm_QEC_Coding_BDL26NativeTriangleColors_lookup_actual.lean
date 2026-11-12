-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_actual
-- name    : QEC.Coding.BDL26NativeTriangleColors.lookup_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:26:03.240387+00:00
-- url     : https://prove2.me/theorems/5f1e8723-4c9d-42f7-966c-cce981eb2647
-- title:
--   BDL26 Native Triangle Colors: lookup actual
-- statement:
--   The BDL26 Native Triangle Colors construction uses the lookup actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L563-L567
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L563-L567

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

theorem QEC.Coding.BDL26NativeTriangleColors.lookup_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (colorOfCodeQ S n (encode S n t)).value=(nativeRow S n t).2 := by sorry
