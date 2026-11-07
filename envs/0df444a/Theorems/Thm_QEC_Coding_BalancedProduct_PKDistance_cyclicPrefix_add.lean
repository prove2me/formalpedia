-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_add
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:05:05.298235+00:00
-- url     : https://prove2.me/theorems/37b7ddc9-939f-458b-9357-a30a35e1926c
-- title:
--   PKDistance: cyclic Prefix add
-- statement:
--   The PKDistance construction uses the cyclic Prefix add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1187-L1194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1187-L1194

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_add
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat)
    (z w : Word (ZMod 2) (I × G)) :
    cyclicPrefix x t (z + w) =
      cyclicPrefix x t z + cyclicPrefix x t w := by sorry
