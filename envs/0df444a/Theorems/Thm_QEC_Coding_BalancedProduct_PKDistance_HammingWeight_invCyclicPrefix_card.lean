-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_invCyclicPrefix_card
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_invCyclicPrefix_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:06:23.060439+00:00
-- url     : https://prove2.me/theorems/e216e980-bb08-49ae-bc4a-367d6cd891fb
-- title:
--   PKDistance: Hamming Weight inv Cyclic Prefix card
-- statement:
--   Exact full-prefix weight in the inverse cyclic orientation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1779-L1792
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1779-L1792

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_invCyclicPrefix_card
    {I : Type u} [Fintype I] (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q)) :
    HammingWeight (cyclicPrefix ((Cyclic.cyclicGenerator q)⁻¹) q z) =
      q * HammingWeight (fibreSum z) := by sorry
