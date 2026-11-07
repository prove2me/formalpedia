-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_le_add_HammingWeight_add
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_le_add_HammingWeight_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:02:53.741193+00:00
-- url     : https://prove2.me/theorems/020d92de-bc20-40ea-8f82-65faec29995c
-- title:
--   PKDistance: Hamming Weight le add Hamming Weight add
-- statement:
--   Over binary words, the later word is bounded by the earlier word plus
--   their difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L338-L358
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L338-L358

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_le_add_HammingWeight_add
    {ι : Type u} [Fintype ι]
    (earlier later : Word (ZMod 2) ι) :
    HammingWeight later ≤
      HammingWeight earlier + HammingWeight (later + earlier) := by sorry
