-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_inverse_coordinates
-- name    : QEC.Coding.BDL26NativeTriangleKeys.inverse_coordinates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T01:35:45.888784+00:00
-- url     : https://prove2.me/theorems/3fec681e-18ab-4b92-a382-a53a6a6c5c80
-- title:
--   BDL26 Native Triangle Keys: inverse coordinates
-- statement:
--   The BDL26 Native Triangle Keys construction uses the inverse coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L310-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L310-L313

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section

theorem QEC.Coding.BDL26NativeTriangleKeys.inverse_coordinates (S : OddScale) (n : ℕ) (k : Fin (triangleCount S n)) :
    ((BDL26NativePresentationGenerator.generatedRefines S n).fIndex ((nativeTriangleIndex S n).symm k).1).val=
        k.val/2 ∧ ((nativeTriangleIndex S n).symm k).2.val=k.val%2 := by sorry
