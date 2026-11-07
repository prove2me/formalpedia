-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_normalizeCyclicFibres_half
-- name    : QEC.Coding.BalancedProduct.PKDistance.normalizeCyclicFibres_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:04:50.621705+00:00
-- url     : https://prove2.me/theorems/9fac1da1-4f8c-41e8-988f-c81363f80266
-- title:
--   PKDistance: normalize Cyclic Fibres half
-- statement:
--   Every normalized cyclic fibre occupies at most half its coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1648-L1654
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L1648-L1654

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

theorem QEC.Coding.BalancedProduct.PKDistance.normalizeCyclicFibres_half
    {I : Type u} {G : Type v} [Fintype G]
    (z : Word (ZMod 2) (I × G)) (i : I) :
    2 * HammingWeight (fun g : G => normalizeCyclicFibres z (i, g)) ≤
      Fintype.card G := by sorry
