-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_missing
-- name    : QEC.Coding.BDL26NativeTriangleColors.lookup_missing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:56:39.188064+00:00
-- url     : https://prove2.me/theorems/91a428bf-d86f-4547-8d99-7cab9bcef29d
-- title:
--   BDL26 Native Triangle Colors: lookup missing
-- statement:
--   The BDL26 Native Triangle Colors construction uses the lookup missing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L569-L573
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L569-L573

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

theorem QEC.Coding.BDL26NativeTriangleColors.lookup_missing (S : OddScale) (n : ℕ) (c : Code) (hc : c∉T S n) :
    (colorOfCodeQ S n c).value=none := by sorry
