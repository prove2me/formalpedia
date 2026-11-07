-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineOrder_ramificationIndex_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_ramificationIndex_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:32:12.978261+00:00
-- url     : https://prove2.me/theorems/f1f2518a-404c-41f9-962c-bf40cbfe6e4a
-- title:
--   Tanner Lifted Product: lps Original Gauss Affine Order ramification Index one
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Affine Order ramification Index one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L34-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L34-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_ramificationIndex_one
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsPrime] :
    q.ramificationIdx (LPSOriginalGaussBase p) = 1 := by sorry
