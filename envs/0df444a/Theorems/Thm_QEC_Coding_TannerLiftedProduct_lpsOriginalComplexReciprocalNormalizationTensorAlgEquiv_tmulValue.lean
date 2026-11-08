-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv_tmulValue
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv_tmulValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:59:12.376584+00:00
-- url     : https://prove2.me/theorems/147d6109-be2e-4605-93bd-0dedba51df6c
-- title:
--   Tanner Lifted Product: lps Original Complex Reciprocal Normalization Tensor Alg Equiv tmul Value
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Reciprocal Normalization Tensor Alg Equiv tmul Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNormalizationComparison.lean#L428-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNormalizationComparison.lean#L428-L432

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary001
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary012
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary016
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary024
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary025
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary026
local notation "BP" => ℂ ⊗[ℚ] Polynomial ℚ
local notation "TB" => ℂ ⊗[ℚ] FQ
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary027
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary029

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv_tmulValue
    (c : ℂ) (x : integralClosure (Polynomial ℚ) FQ) :
    (lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv N hN (c ⊗ₜ[ℚ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val := by sorry
