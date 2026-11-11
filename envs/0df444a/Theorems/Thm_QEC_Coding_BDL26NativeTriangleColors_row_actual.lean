-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_row_actual
-- name    : QEC.Coding.BDL26NativeTriangleColors.row_actual
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:28:21.948808+00:00
-- url     : https://prove2.me/theorems/006bd124-e2da-48b3-8f40-7e7cc2b686be
-- title:
--   BDL26 Native Triangle Colors: row actual
-- statement:
--   The BDL26 Native Triangle Colors construction uses the row actual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L497-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L497-L513

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

theorem QEC.Coding.BDL26NativeTriangleColors.row_actual (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (colorRowQ (BDL26NativeSupportMetadata.atlasQ S n).value (encode S n t)).value=
      nativeRow S n t := by sorry
