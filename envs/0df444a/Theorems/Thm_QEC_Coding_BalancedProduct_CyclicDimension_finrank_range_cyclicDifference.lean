-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_finrank_range_cyclicDifference
-- name    : QEC.Coding.BalancedProduct.CyclicDimension.finrank_range_cyclicDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:53:15.757314+00:00
-- url     : https://prove2.me/theorems/6c81bd8f-ae9b-4f6b-a2f3-25893eb5bf4e
-- title:
--   Cyclic Dimension: finrank range cyclic Difference
-- statement:
--   Exact rank of the cyclic difference on `|I|` disjoint `q`-cycles.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L108-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L108-L125

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u

theorem QEC.Coding.BalancedProduct.CyclicDimension.finrank_range_cyclicDifference
    (q : Nat) [NeZero q] (I : Type u) [Fintype I] :
    Module.finrank (ZMod 2) (LinearMap.range (cyclicDifference q I)) =
      Fintype.card I * (q - 1) := by sorry
