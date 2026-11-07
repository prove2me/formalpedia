-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_cyclicShift
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_cyclicShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:49.965602+00:00
-- url     : https://prove2.me/theorems/3b1211be-823a-41b0-a3d0-1b8a09ecd3d9
-- title:
--   PKDistance: cyclic Prefix cyclic Shift
-- statement:
--   Prefixing commutes with one further shift by the same cyclic generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1197-L1208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1197-L1208

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x t (cyclicShift x z) =
      cyclicShift x (cyclicPrefix x t z) := by sorry
