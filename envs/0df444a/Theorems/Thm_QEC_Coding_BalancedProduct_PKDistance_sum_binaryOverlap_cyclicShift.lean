-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_sum_binaryOverlap_cyclicShift
-- name    : QEC.Coding.BalancedProduct.PKDistance.sum_binaryOverlap_cyclicShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:08.262708+00:00
-- url     : https://prove2.me/theorems/344f71a5-4f92-4e24-952e-7dd88bc6b7d7
-- title:
--   PKDistance: sum binary Overlap cyclic Shift
-- statement:
--   Exact autocorrelation count: summing the overlap over every cyclic shift
--   gives the sum of the squares of the fibre weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L183-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L183-L218

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

theorem QEC.Coding.BalancedProduct.PKDistance.sum_binaryOverlap_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G)) :
    (∑ t, binaryOverlap z (cyclicShift t z)) =
      ∑ i, fibreWeight z i * fibreWeight z i := by sorry
