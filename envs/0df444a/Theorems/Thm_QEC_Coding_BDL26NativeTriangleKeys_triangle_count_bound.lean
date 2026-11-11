-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_triangle_count_bound
-- name    : QEC.Coding.BDL26NativeTriangleKeys.triangle_count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T23:55:37.991925+00:00
-- url     : https://prove2.me/theorems/c7e80c4a-b995-4a96-9a1c-f1c59e3f4d05
-- title:
--   BDL26 Native Triangle Keys: triangle count bound
-- statement:
--   Extracted from the real retained representation, without a caller budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L467-L472
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L467-L472

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.triangle_count_bound (S : OddScale) (n : ℕ) :
    triangleCount S n≤(n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15 := by sorry
