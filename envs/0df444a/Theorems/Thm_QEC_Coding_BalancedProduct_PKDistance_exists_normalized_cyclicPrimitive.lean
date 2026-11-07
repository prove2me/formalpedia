-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_normalized_cyclicPrimitive
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_normalized_cyclicPrimitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:10.280019+00:00
-- url     : https://prove2.me/theorems/923b9a25-a777-4973-a418-7088cbb3a884
-- title:
--   PKDistance: exists normalized cyclic Primitive
-- statement:
--   Zero fibre augmentation has a normalized `1+x` primitive with the exact
--   per-fibre half-weight condition used in PK20 Lemma `lm:autcorr`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1687-L1699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1687-L1699

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

theorem QEC.Coding.BalancedProduct.PKDistance.exists_normalized_cyclicPrimitive
    {I : Type u} (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (z : Word (ZMod 2) (I × Cyclic.CyclicGroup q))
    (hzero : fibreSum z = 0) :
    ∃ h : Word (ZMod 2) (I × Cyclic.CyclicGroup q),
      z = h + cyclicShift (Cyclic.cyclicGenerator q) h ∧
      ∀ i, 2 * fibreWeight h i ≤ q := by sorry
