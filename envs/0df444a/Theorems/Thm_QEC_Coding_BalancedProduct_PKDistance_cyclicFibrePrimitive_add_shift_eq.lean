-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicFibrePrimitive_add_shift_eq
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclicFibrePrimitive_add_shift_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:05:16.068818+00:00
-- url     : https://prove2.me/theorems/4897d657-f980-4dee-87d7-11b67ee60ebd
-- title:
--   PKDistance: cyclic Fibre Primitive add shift eq
-- statement:
--   A word with zero sum on every canonical cyclic fibre is the concrete
--   `1+x` cyclic difference of its explicit prefix primitive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1604-L1639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1604-L1639

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclicFibrePrimitive_add_shift_eq
    {I : Type u} (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : fibreSum z = 0) :
    cyclicFibrePrimitive q z +
        cyclicShift (Cyclic.cyclicGenerator q) (cyclicFibrePrimitive q z) =
      z := by sorry
