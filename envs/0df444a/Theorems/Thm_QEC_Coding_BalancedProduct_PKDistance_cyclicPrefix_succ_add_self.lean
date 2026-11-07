-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_succ_add_self
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_succ_add_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:50.807423+00:00
-- url     : https://prove2.me/theorems/da06d0fe-22a2-4ce1-aaf0-6e2b94cd30b7
-- title:
--   PKDistance: cyclic Prefix succ add self
-- statement:
--   Consecutive prefix sums differ by one translated copy of the input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L427-L434
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L427-L434

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_succ_add_self
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x (t + 1) z + cyclicPrefix x t z =
      cyclicShift (x ^ t) z := by sorry
