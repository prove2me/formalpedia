-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_normalizeCyclicFibres_add_shift
-- name    : QEC.Coding.BalancedProduct.PKDistance.normalizeCyclicFibres_add_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:05:00.993645+00:00
-- url     : https://prove2.me/theorems/ff76c73d-4e43-43a8-a32d-6e2676aa0dac
-- title:
--   PKDistance: normalize Cyclic Fibres add shift
-- statement:
--   Fibrewise normalization changes a word only by constants and therefore
--   does not change its `1+x` cyclic difference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1658-L1683
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1658-L1683

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

theorem QEC.Coding.BalancedProduct.PKDistance.normalizeCyclicFibres_add_shift
    {I : Type u} {G : Type v} [Group G] [Fintype G]
    (x : G) (z : Word (ZMod 2) (I × G)) :
    normalizeCyclicFibres z + cyclicShift x (normalizeCyclicFibres z) =
      z + cyclicShift x z := by sorry
