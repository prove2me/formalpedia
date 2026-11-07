-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineToGenerated_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:16:16.661194+00:00
-- url     : https://prove2.me/theorems/dad5841d-c312-447c-a881-3b8fffc36d79
-- title:
--   Tanner Lifted Product: lps Original Gauss Affine To Generated root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Affine To Generated root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussLocalOrder.lean#L605-L621
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussLocalOrder.lean#L605-L621

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
open scoped TensorProduct

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineToGenerated_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalGaussAffineToGenerated N hN p
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val) =
      lpsOriginalJNInFractionField N hN := by sorry
