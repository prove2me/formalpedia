-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_cyclicInvariant
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_cyclicInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:03:29.170537+00:00
-- url     : https://prove2.me/theorems/dca9e8e5-007f-4ae4-9c40-57b0f24fbf25
-- title:
--   PKDistance: Hamming Weight cyclic Invariant
-- statement:
--   Exact weight of a generator-invariant cyclic word: every occupied fibre
--   contributes all `q` coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1006-L1022
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1006-L1022

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_cyclicInvariant
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q) z = 0) :
    HammingWeight z = q * HammingWeight (fun i => z (i, 1)) := by sorry
