-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_output_readback
-- name    : QEC.Coding.BDL26NativeTriangleColors.output_readback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:28:06.913206+00:00
-- url     : https://prove2.me/theorems/946681f1-6700-4a6f-bef9-9594d886cc2c
-- title:
--   BDL26 Native Triangle Colors: output readback
-- statement:
--   The BDL26 Native Triangle Colors construction uses the output readback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L515-L519
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L515-L519

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

theorem QEC.Coding.BDL26NativeTriangleColors.output_readback (S : OddScale) (n : ℕ) (t : Triangle (P S n)) :
    (colorsQ S n).value[(BDL26NativeTriangleKeys.nativeTriangleIndex S n t).val]?=
      some (nativeRow S n t) := by sorry
