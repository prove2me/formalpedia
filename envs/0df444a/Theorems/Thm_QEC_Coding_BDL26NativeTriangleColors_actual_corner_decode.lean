-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_actual_corner_decode
-- name    : QEC.Coding.BDL26NativeTriangleColors.actual_corner_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:28:21.98586+00:00
-- url     : https://prove2.me/theorems/c1402977-b292-4af9-bd8d-2662dca862b4
-- title:
--   BDL26 Native Triangle Colors: actual corner decode
-- statement:
--   The BDL26 Native Triangle Colors construction uses the actual corner decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L423-L426
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleColors.lean#L423-L426

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

theorem QEC.Coding.BDL26NativeTriangleColors.actual_corner_decode (S : OddScale) (n : ℕ) (t : Triangle (P S n)) (i : Fin 3) :
    BDL26NativeStateRows.decode S n (tripleAt (corners S n t) i)=triangleVertex (P S n) t i := by sorry
