-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineOrder_specialFiber_nontrivial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_specialFiber_nontrivial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:33:20.091673+00:00
-- url     : https://prove2.me/theorems/8c595c9d-62c6-4de5-a8ef-9190fb47a559
-- title:
--   Tanner Lifted Product: lps Original Gauss Affine Order special Fiber nontrivial
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Affine Order special Fiber nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L74-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L74-L93

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_specialFiber_nontrivial
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Nontrivial (LPSOriginalGaussAffineOrder N hN p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))) := by sorry
