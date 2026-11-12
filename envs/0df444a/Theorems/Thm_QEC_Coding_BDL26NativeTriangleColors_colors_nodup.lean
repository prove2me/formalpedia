-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_nodup
-- name    : QEC.Coding.BDL26NativeTriangleColors.colors_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:30:19.962138+00:00
-- url     : https://prove2.me/theorems/ce50da70-05bf-416e-a7b4-6e8d7fbb74d9
-- title:
--   BDL26 Native Triangle Colors: colors nodup
-- statement:
--   The BDL26 Native Triangle Colors construction uses the colors nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L307-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L307-L310

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.colors_nodup (S : OddScale) (n : ℕ) : (colorsQ S n).value.Nodup := by sorry
