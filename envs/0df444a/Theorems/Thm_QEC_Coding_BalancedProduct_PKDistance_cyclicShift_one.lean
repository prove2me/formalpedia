-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclicShift_one
-- name    : QEC.Coding.BalancedProduct.PKDistance.cyclicShift_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:11.234735+00:00
-- url     : https://prove2.me/theorems/c429ff01-89aa-4baf-9e37-d488acaddf58
-- title:
--   PKDistance: cyclic Shift one
-- statement:
--   The PKDistance construction uses the cyclic Shift one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L445-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L445-L450

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

theorem QEC.Coding.BalancedProduct.PKDistance.cyclicShift_one
    {I : Type u} {G : Type v} [Group G]
    (z : Word (ZMod 2) (I × G)) :
    cyclicShift (1 : G) z = z := by sorry
