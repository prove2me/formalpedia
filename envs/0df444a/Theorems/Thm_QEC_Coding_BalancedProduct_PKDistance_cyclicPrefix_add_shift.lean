-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicPrefix_add_shift
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_add_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:03:09.850255+00:00
-- url     : https://prove2.me/theorems/4cddfc8b-3e91-468d-baae-0c6e94f192c2
-- title:
--   PKDistance: cyclic Prefix add shift
-- statement:
--   The binary geometric-series identity
--   `(1 + x)(1 + ⋯ + x^(t-1)) = 1 + x^t`, expressed on cyclic words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L464-L488
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L464-L488

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclicPrefix_add_shift
    {I : Type u} {G : Type v} [Group G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    cyclicPrefix x t z + cyclicShift x (cyclicPrefix x t z) =
      z + cyclicShift (x ^ t) z := by sorry
