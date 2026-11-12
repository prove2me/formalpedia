-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_output_sound
-- name    : QEC.Coding.BDL26NativeTriangleColors.output_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:38:06.833199+00:00
-- url     : https://prove2.me/theorems/9eb89560-e176-4d04-97f8-3204ea845cad
-- title:
--   BDL26 Native Triangle Colors: output sound
-- statement:
--   All rows succeed internally, preserve the full code and typed corners, and
--   compute all three ranks; actual valence discharges the fixed palette bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L546-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L546-L551

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

theorem QEC.Coding.BDL26NativeTriangleColors.output_sound (S : OddScale) (n : ℕ)
    (r : ColorRow (BDL26NativeStateRows.Index S n)) (hr : r∈(colorsQ S n).value) :
    ∃t : Triangle (P S n),r=nativeRow S n t ∧
      ∀i : Fin 3,nativeColor S n t i<56 := by sorry
