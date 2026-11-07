-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_normalized_invCyclicPrimitive
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_normalized_invCyclicPrimitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:52.286453+00:00
-- url     : https://prove2.me/theorems/7c7bc6db-227c-42e4-9136-3638504be105
-- title:
--   PKDistance: exists normalized inv Cyclic Primitive
-- statement:
--   The same normalized primitive in the opposite cyclic orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1702-L1715
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1702-L1715

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_normalized_invCyclicPrimitive
    {I : Type u} (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : fibreSum z = 0) :
    ∃ h : Word (ZMod 2) (I × Cyclic.CyclicGroup q),
      z = h + cyclicShift ((Cyclic.cyclicGenerator q)⁻¹) h ∧
      ∀ i, 2 * fibreWeight h i ≤ q := by sorry
