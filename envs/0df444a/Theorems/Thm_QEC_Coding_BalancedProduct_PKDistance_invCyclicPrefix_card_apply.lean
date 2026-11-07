-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_invCyclicPrefix_card_apply
-- name    : QEC.Coding.BalancedProduct.PKDistance.invCyclicPrefix_card_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:15.914694+00:00
-- url     : https://prove2.me/theorems/f6e7a3a1-44a5-4787-b214-50bdd1cd0625
-- title:
--   PKDistance: inv Cyclic Prefix card apply
-- statement:
--   The inverse generator also traverses every cyclic coordinate exactly
--   once, with the same full-prefix endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1741-L1759
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1741-L1759

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

theorem QEC.Coding.BalancedProduct.PKDistance.invCyclicPrefix_card_apply
    {I : Type u} (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (i : I) (g : Cyclic.CyclicGroup q) :
    cyclicPrefix ((Cyclic.cyclicGenerator q)⁻¹) q z (i, g) = fibreSum z i := by sorry
