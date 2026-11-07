-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_card_apply
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_card_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:11.467892+00:00
-- url     : https://prove2.me/theorems/58f5bc17-2fc3-492c-b58b-7f3333000615
-- title:
--   PKDistance: cyclic Prefix card apply
-- statement:
--   A length-`q` prefix of the canonical generator traverses every element of
--   `CyclicGroup q` exactly once, so the result is constant on each fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1719-L1737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1719-L1737

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_card_apply
    {I : Type u} (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (i : I) (g : Cyclic.CyclicGroup q) :
    cyclicPrefix (Cyclic.cyclicGenerator q) q z (i, g) = fibreSum z i := by sorry
