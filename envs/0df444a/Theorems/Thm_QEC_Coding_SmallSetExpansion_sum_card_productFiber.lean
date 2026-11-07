-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_sum_card_productFiber
-- name    : QEC.Coding.SmallSetExpansion.sum_card_productFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:58.3732+00:00
-- url     : https://prove2.me/theorems/672f27d9-518c-4972-b975-a81026c023e5
-- title:
--   Small Set Expansion: sum card product Fiber
-- statement:
--   A product finset is the disjoint union of its first-coordinate fibers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L133-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/SmallSetExpansion.lean#L133-L156

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}

theorem QEC.Coding.SmallSetExpansion.sum_card_productFiber
    {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (S : Finset (I × V)) :
    ∑ i, (productFiber S i).card = S.card := by sorry
