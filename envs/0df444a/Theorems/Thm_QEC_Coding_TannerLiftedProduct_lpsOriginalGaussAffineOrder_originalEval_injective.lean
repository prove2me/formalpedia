-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineOrder_originalEval_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_originalEval_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T04:16:01.996218+00:00
-- url     : https://prove2.me/theorems/3144c555-1285-4e37-8458-5b3155b8f3a8
-- title:
--   Tanner Lifted Product: lps Original Gauss Affine Order original Eval injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Affine Order original Eval injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussLocalOrder.lean#L441-L461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussLocalOrder.lean#L441-L461

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalGaussPrime_isPrime
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalGaussPrime_principal

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineOrder_originalEval_injective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalGaussAffineOrder_originalEval N hN p) := by sorry
