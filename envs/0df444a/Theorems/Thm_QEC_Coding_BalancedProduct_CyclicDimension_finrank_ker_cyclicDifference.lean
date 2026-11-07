-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_finrank_ker_cyclicDifference
-- name    : QEC.Coding.BalancedProduct.CyclicDimension.finrank_ker_cyclicDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:54:26.289567+00:00
-- url     : https://prove2.me/theorems/5677e963-560d-4568-bc20-1e5c4ce8c045
-- title:
--   Cyclic Dimension: finrank ker cyclic Difference
-- statement:
--   The Cyclic Dimension construction uses the finrank ker cyclic Difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L100-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/CyclicDimension.lean#L100-L105

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u

theorem QEC.Coding.BalancedProduct.CyclicDimension.finrank_ker_cyclicDifference
    (q : Nat) [NeZero q] (I : Type u) [Fintype I] :
    Module.finrank (ZMod 2) (LinearMap.ker (cyclicDifference q I)) =
      Fintype.card I := by sorry
