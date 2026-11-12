-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_output_unique
-- name    : QEC.Coding.BDL26NativeTriangleColors.output_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T05:54:46.758475+00:00
-- url     : https://prove2.me/theorems/168932ba-3945-4192-88b2-d3f9613585fe
-- title:
--   BDL26 Native Triangle Colors: output unique
-- statement:
--   The BDL26 Native Triangle Colors construction uses the output unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L527-L542
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L527-L542

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

theorem QEC.Coding.BDL26NativeTriangleColors.output_unique (S : OddScale) (n : ℕ)
    (r : ColorRow (BDL26NativeStateRows.Index S n)) (hr : r∈(colorsQ S n).value) :
    ∃!t : Triangle (P S n),nativeRow S n t=r := by sorry
