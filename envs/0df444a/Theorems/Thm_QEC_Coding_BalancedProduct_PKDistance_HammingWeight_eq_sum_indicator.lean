-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_eq_sum_indicator
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_eq_sum_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:58:33.77168+00:00
-- url     : https://prove2.me/theorems/c0d2d325-2658-48d0-a2a1-bdbbe1df87cb
-- title:
--   PKDistance: Hamming Weight eq sum indicator
-- statement:
--   Hamming weight written as a sum of coordinate indicators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L92-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L92-L97

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_eq_sum_indicator
    {F : Type u} [Zero F] [DecidableEq F]
    {ι : Type v} [Fintype ι] (z : Word F ι) :
    HammingWeight z = ∑ i, if z i ≠ 0 then 1 else 0 := by sorry
