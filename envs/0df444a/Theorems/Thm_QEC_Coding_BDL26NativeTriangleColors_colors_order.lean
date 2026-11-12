-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_order
-- name    : QEC.Coding.BDL26NativeTriangleColors.colors_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:54:23.007399+00:00
-- url     : https://prove2.me/theorems/6b314b9b-29a9-4de3-aa01-14a52c40b7c3
-- title:
--   BDL26 Native Triangle Colors: colors order
-- statement:
--   The BDL26 Native Triangle Colors construction uses the colors order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L296-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L296-L305

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.colors_order (S : OddScale) (n : ℕ) :
    (colorsQ S n).value.map Prod.fst=T S n := by sorry
