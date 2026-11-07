-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:35:33.801199+00:00
-- url     : https://prove2.me/theorems/9e7598c0-bea1-4d1f-b880-a207c1ea1cf5
-- title:
--   Tanner Lifted Product: lps Original Integer Zero Chart Complex Normalization Alg Equiv tmul Value
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Zero Chart Complex Normalization Alg Equiv tmul Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean#L819-L832
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean#L819-L832

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
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary062
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary063
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary064
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary065
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary066
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary067
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary068
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary069
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary070
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary071
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary072
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary073
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary074
local notation "IZ" => integralClosure (Polynomial ℤ) FQ
local notation "IQ" => integralClosure (Polynomial ℚ) FQ
local notation "IC" => integralClosure (Polynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary075
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary076

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue
    (c : ℂ) (x : lpsOriginalIntegerNormalZeroChart N hN) :
    (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN (c ⊗ₜ[ℤ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val := by sorry
