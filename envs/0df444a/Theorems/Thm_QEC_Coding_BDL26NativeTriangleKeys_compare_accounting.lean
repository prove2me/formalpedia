-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_compare_accounting
-- name    : QEC.Coding.BDL26NativeTriangleKeys.compare_accounting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T01:25:46.771212+00:00
-- url     : https://prove2.me/theorems/11023fa0-fabc-4c96-a2c9-1871da148c22
-- title:
--   BDL26 Native Triangle Keys: compare accounting
-- statement:
--   Exact pair accounting keeps both closed lookups in every branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L66-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeTriangleKeys.lean#L66-L74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph

theorem QEC.Coding.BDL26NativeTriangleKeys.compare_accounting (S : OddScale) (n : ℕ) (a b : Code) :
    operations (compareCodesQ S n a b)=
        operations (keyOfCodeQ S n a)+operations (keyOfCodeQ S n b)+
          (if (keyOfCodeQ S n a).1.isSome && (keyOfCodeQ S n b).1.isSome then 4 else 2) ∧
      allocations (compareCodesQ S n a b)=
        allocations (keyOfCodeQ S n a)+allocations (keyOfCodeQ S n b)+
          (if (keyOfCodeQ S n a).1.isSome && (keyOfCodeQ S n b).1.isSome then 1 else 0) := by sorry
