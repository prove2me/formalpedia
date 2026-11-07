-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_add_cyclicShift_le_two_mul
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_add_cyclicShift_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:53.108809+00:00
-- url     : https://prove2.me/theorems/b882c408-d324-406e-89b0-7ed8af0095db
-- title:
--   PKDistance: Hamming Weight add cyclic Shift le two mul
-- statement:
--   The elementary triangle estimate used for every cyclic difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L62-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L62-L73

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_add_cyclicShift_le_two_mul
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G] (t : G)
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight (z + cyclicShift t z) ≤ 2 * HammingWeight z := by sorry
