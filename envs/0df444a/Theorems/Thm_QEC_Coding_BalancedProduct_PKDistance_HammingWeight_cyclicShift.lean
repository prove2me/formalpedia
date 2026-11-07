-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_cyclicShift
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_cyclicShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:36.206458+00:00
-- url     : https://prove2.me/theorems/de13184e-fa5f-4261-b74b-6a273a08fdb5
-- title:
--   PKDistance: Hamming Weight cyclic Shift
-- statement:
--   The PKDistance construction uses the Hamming Weight cyclic Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L52-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L52-L59

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_cyclicShift
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G] (t : G)
    (z : Word (ZMod 2) (I × G)) :
    HammingWeight (cyclicShift t z) = HammingWeight z := by sorry
