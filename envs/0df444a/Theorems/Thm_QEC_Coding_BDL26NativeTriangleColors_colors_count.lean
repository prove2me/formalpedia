-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_count
-- name    : QEC.Coding.BDL26NativeTriangleColors.colors_count
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:54:02.92553+00:00
-- url     : https://prove2.me/theorems/ab7fabf7-8356-4e9e-9b31-e349d50ea4b8
-- title:
--   BDL26 Native Triangle Colors: colors count
-- statement:
--   The BDL26 Native Triangle Colors construction uses the colors count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L312-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L312-L315

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.colors_count (S : OddScale) (n : ℕ) :
    (colorsQ S n).value.length=BDL26NativeTriangleKeys.triangleCount S n := by sorry
