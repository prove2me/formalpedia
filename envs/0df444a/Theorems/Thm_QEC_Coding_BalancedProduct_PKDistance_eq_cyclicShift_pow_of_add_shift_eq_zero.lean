-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_eq_cyclicShift_pow_of_add_shift_eq_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.eq_cyclicShift_pow_of_add_shift_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:02.725947+00:00
-- url     : https://prove2.me/theorems/79340f69-8b1e-46ae-8ecc-c884ccd115fa
-- title:
--   PKDistance: eq cyclic Shift pow of add shift eq zero
-- statement:
--   Generator invariance propagates to every nonnegative power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L968-L982
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L968-L982

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

theorem QEC.Coding.BalancedProduct.PKDistance.eq_cyclicShift_pow_of_add_shift_eq_zero
    {I : Type u} {G : Type v} [Group G]
    (x : G) (z : Word (ZMod 2) (I × G))
    (hzero : z + cyclicShift x z = 0) (t : Nat) :
    z = cyclicShift (x ^ t) z := by sorry
