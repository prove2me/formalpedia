-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussNormalizationEquiv_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussNormalizationEquiv_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:16:10.898406+00:00
-- url     : https://prove2.me/theorems/89e0388a-7fe5-4ae9-9c16-4ec5bc27818f
-- title:
--   Tanner Lifted Product: lps Original Gauss Normalization Equiv root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Normalization Equiv root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussLocalOrder.lean#L645-L670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussLocalOrder.lean#L645-L670

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussNormalizationEquiv_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
      ((lpsOriginalGaussAffineToGenerated N hN p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder N hN p))).toAlgebra
    ((lpsOriginalGaussNormalizationEquiv N hN p hpN
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))).val.val) =
      lpsOriginalJNInFractionField N hN := by sorry
