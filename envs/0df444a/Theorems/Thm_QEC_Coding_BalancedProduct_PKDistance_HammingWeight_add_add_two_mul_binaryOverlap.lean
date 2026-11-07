-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_add_add_two_mul_binaryOverlap
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_add_add_two_mul_binaryOverlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:43.352292+00:00
-- url     : https://prove2.me/theorems/3debaa8a-4165-40b6-9ede-95e60d93c450
-- title:
--   PKDistance: Hamming Weight add add two mul binary Overlap
-- statement:
--   Binary inclusion--exclusion: XOR weight plus twice the overlap is the
--   sum of the two input weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L101-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L101-L124

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_add_add_two_mul_binaryOverlap
    {ι : Type u} [Fintype ι]
    (left right : Word (ZMod 2) ι) :
    HammingWeight (left + right) + 2 * binaryOverlap left right =
      HammingWeight left + HammingWeight right := by sorry
