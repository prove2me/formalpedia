-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexAffineNormalizationTensorAlgEquiv_tmulValue
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexAffineNormalizationTensorAlgEquiv_tmulValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:36:05.103119+00:00
-- url     : https://prove2.me/theorems/34318608-b95e-4249-8a4d-dd2e2f1651a0
-- title:
--   Tanner Lifted Product: lps Original Complex Affine Normalization Tensor Alg Equiv tmul Value
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Affine Normalization Tensor Alg Equiv tmul Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean#L659-L663
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean#L659-L663

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
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary040
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary043
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local notation "BP" => ℂ ⊗[ℚ] Polynomial ℚ
local notation "TB" => ℂ ⊗[ℚ] FQ
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary044
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary046
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary051
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary052
attribute [local instance] QEC.Coding.TannerLiftedProduct.zeroNormalizationDictionary053

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexAffineNormalizationTensorAlgEquiv_tmulValue
    (c : ℂ) (x : integralClosure (Polynomial ℚ) FQ) :
    (lpsOriginalComplexAffineNormalizationTensorAlgEquiv N hN (c ⊗ₜ[ℚ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val := by sorry
