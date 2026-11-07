-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_cyclicPrefix_step
-- name    : QEC.Coding.BalancedProduct.PKDistance.HammingWeight_cyclicPrefix_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:44.897749+00:00
-- url     : https://prove2.me/theorems/f7acb7fb-9f6c-469e-9c02-6fd173686da3
-- title:
--   PKDistance: Hamming Weight cyclic Prefix step
-- statement:
--   Every prefix step has exactly the original word's Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L437-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L437-L443

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

theorem QEC.Coding.BalancedProduct.PKDistance.HammingWeight_cyclicPrefix_step
    {I : Type u} {G : Type v} [Group G]
    [Fintype I] [Fintype G]
    (x : G) (t : Nat) (z : Word (ZMod 2) (I × G)) :
    HammingWeight (cyclicPrefix x (t + 1) z + cyclicPrefix x t z) =
      HammingWeight z := by sorry
