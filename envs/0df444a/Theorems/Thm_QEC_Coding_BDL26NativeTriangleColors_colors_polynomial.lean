-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_colors_polynomial
-- name    : QEC.Coding.BDL26NativeTriangleColors.colors_polynomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:56:00.346821+00:00
-- url     : https://prove2.me/theorems/ed58814d-f1d4-4c79-99ad-4ca206067b52
-- title:
--   BDL26 Native Triangle Colors: colors polynomial
-- statement:
--   The BDL26 Native Triangle Colors construction uses the colors polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L329-L366
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L329-L366

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G

theorem QEC.Coding.BDL26NativeTriangleColors.colors_polynomial (S : OddScale) (n : ℕ) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (colorsQ S n).operations≤A+275*B^2+103*B+4 ∧
      (colorsQ S n).allocations≤A+4*B^2+19*B+2 := by sorry
