-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv_tmulValue
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv_tmulValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:34:52.899523+00:00
-- url     : https://prove2.me/theorems/ed5bfe37-9faa-47f3-b0cf-18a5c7c59882
-- title:
--   Tanner Lifted Product: lps Original Integer Zero Normalization Rational Tensor Alg Equiv tmul Value
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Zero Normalization Rational Tensor Alg Equiv tmul Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean#L766-L769
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean#L766-L769

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary054
variable (N : ℕ) (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "BP" => ℚ ⊗[ℤ] Polynomial ℤ
local notation "TB" => ℚ ⊗[ℤ] FQ
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary055
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary056
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary057
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary058
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary059
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary060
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary061

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv_tmulValue
    (q : ℚ) (x : integralClosure (Polynomial ℤ) FQ) :
    (lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv N hN (q ⊗ₜ[ℤ] x)).val =
      q • x.val := by sorry
