-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_polynomial
-- name    : QEC.Coding.BDL26NativeTriangleColors.lookup_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T08:31:24.611694+00:00
-- url     : https://prove2.me/theorems/d2827ea4-ea8e-47ee-9a79-8ceb1df6dd7a
-- title:
--   BDL26 Native Triangle Colors: lookup polynomial
-- statement:
--   The BDL26 Native Triangle Colors construction uses the lookup polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L584-L594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L584-L594

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

theorem QEC.Coding.BDL26NativeTriangleColors.lookup_polynomial (S : OddScale) (n : ℕ) (c : Code) :
    let B := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    let A := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    (colorOfCodeQ S n c).operations≤A+275*B^2+146*B+7 ∧
      (colorOfCodeQ S n c).allocations≤A+4*B^2+19*B+2 := by sorry
