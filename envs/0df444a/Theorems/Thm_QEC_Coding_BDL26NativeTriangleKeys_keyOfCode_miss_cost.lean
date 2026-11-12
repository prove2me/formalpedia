-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_miss_cost
-- name    : QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_miss_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:43:24.918702+00:00
-- url     : https://prove2.me/theorems/98631041-cfbb-4a2d-9768-ac78007ddcdd
-- title:
--   BDL26 Native Triangle Keys: key Of Code miss cost
-- statement:
--   Failure is paid by the same generator and every complete-record rejection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L504-L528
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L504-L528

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_miss_cost (S : OddScale) (n : ℕ) (c : Code)
    (hc : c∉(BDL26NativePresentationGenerator.setupQ S n).1.triangles) :
    (keyOfCodeQ S n c).1=none ∧
      operations (keyOfCodeQ S n c)=(BDL26NativePresentationGenerator.setupQ S n).2+53*triangleCount S n+6 ∧
      allocations (keyOfCodeQ S n c)=BDL26NativePresentationGenerator.allocatedRecords S n+2*triangleCount S n+2 := by sorry
