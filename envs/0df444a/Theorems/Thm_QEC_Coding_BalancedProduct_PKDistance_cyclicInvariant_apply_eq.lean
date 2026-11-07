-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicInvariant_apply_eq
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclicInvariant_apply_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:00.669256+00:00
-- url     : https://prove2.me/theorems/6d2e505b-04d4-4a05-bccc-785b2312ba0c
-- title:
--   PKDistance: cyclic Invariant apply eq
-- statement:
--   A binary word invariant under the canonical generator of `CyclicGroup q`
--   is constant on each cyclic fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L986-L1002
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L986-L1002

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclicInvariant_apply_eq
    {I : Type u} (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q) z = 0)
    (i : I) (g g' : Cyclic.CyclicGroup q) :
    z (i, g) = z (i, g') := by sorry
