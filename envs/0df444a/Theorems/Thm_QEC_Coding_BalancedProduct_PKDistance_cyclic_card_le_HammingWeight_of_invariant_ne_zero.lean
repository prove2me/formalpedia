-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclic_card_le_HammingWeight_of_invariant_ne_zero
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclic_card_le_HammingWeight_of_invariant_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:32.647284+00:00
-- url     : https://prove2.me/theorems/ba150e02-54e1-4081-b3bb-007987d143fd
-- title:
--   PKDistance: cyclic card le Hamming Weight of invariant ne zero
-- statement:
--   A nonzero generator-invariant cyclic word therefore has weight at least
--   the full cyclic-fibre size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1026-L1044
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1026-L1044

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclic_card_le_HammingWeight_of_invariant_ne_zero
    {I : Type u} [Fintype I]
    (q : Nat) [NeZero q]
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : z + cyclicShift (Cyclic.cyclicGenerator q) z = 0)
    (hne : z ≠ 0) :
    q ≤ HammingWeight z := by sorry
