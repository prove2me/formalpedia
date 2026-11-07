-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineOrder_etale
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_etale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:26:59.50652+00:00
-- url     : https://prove2.me/theorems/9bd48905-9ca4-44b0-a552-c3dae945d824
-- title:
--   Tanner Lifted Product: lps Original Gauss Affine Order etale
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Affine Order etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L26-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L26-L32

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_etale
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    Algebra.Etale (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p) := by sorry
