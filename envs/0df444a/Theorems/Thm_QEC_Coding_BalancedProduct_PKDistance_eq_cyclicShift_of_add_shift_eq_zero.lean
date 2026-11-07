-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_eq_cyclicShift_of_add_shift_eq_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.eq_cyclicShift_of_add_shift_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:00:38.364707+00:00
-- url     : https://prove2.me/theorems/6b74e079-c1ea-4d1e-b40b-e62aa87e43d9
-- title:
--   PKDistance: eq cyclic Shift of add shift eq zero
-- statement:
--   Over binary coefficients, a word whose `1+x` cyclic difference vanishes
--   is fixed by the generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L955-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L955-L965

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

theorem QEC.Coding.BalancedProduct.PKDistance.eq_cyclicShift_of_add_shift_eq_zero
    {I : Type u} {G : Type v} [Group G]
    (x : G) (z : Word (ZMod 2) (I × G))
    (hzero : z + cyclicShift x z = 0) :
    z = cyclicShift x z := by sorry
