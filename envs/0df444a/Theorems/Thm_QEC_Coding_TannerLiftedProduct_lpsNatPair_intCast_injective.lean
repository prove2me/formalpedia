-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatPair_intCast_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsNatPair_intCast_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:49:37.704026+00:00
-- url     : https://prove2.me/theorems/666411e8-6b60-4975-96f4-db5c6c40f3d7
-- title:
--   Tanner Lifted Product: lps Nat Pair int Cast injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Nat Pair int Cast injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L163-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSIntegerThreeSquareCount.lean#L163-L170

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsNatPair_intCast_injective :
    Function.Injective (fun a : ℕ × ℕ => ((a.1 : ℤ), (a.2 : ℤ))) := by sorry
