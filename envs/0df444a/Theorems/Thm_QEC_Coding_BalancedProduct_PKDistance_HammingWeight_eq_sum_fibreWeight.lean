-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_eq_sum_fibreWeight
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_eq_sum_fibreWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:01:53.696604+00:00
-- url     : https://prove2.me/theorems/6dbd8071-fb4b-4550-9af3-3ffca7316eda
-- title:
--   PKDistance: Hamming Weight eq sum fibre Weight
-- statement:
--   Total weight is the sum of the weights of its cyclic fibres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L142-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L142-L149

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_eq_sum_fibreWeight
    {I : Type u} {G : Type v} [Fintype I] [Fintype G]
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight z = ∑ i, fibreWeight z i := by sorry
