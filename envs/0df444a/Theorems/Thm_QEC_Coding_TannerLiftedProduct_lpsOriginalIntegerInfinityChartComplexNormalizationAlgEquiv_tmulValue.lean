-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:12:41.208422+00:00
-- url     : https://prove2.me/theorems/f1897080-eb2a-4f14-94d2-d0199bddb67e
-- title:
--   Tanner Lifted Product: lps Original Integer Infinity Chart Complex Normalization Alg Equiv tmul Value
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Infinity Chart Complex Normalization Alg Equiv tmul Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNormalizationComparison.lean#L589-L602
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNormalizationComparison.lean#L589-L602

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary043
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary044
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary046
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary051
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary052
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary053
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary054
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary055
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary056
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary057
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary058
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary059
local notation "IZ" => integralClosure (Polynomial ℤ) FQ
local notation "IQ" => integralClosure (Polynomial ℚ) FQ
local notation "IC" => integralClosure (Polynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary060
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary061

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue
    (c : ℂ) (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN (c ⊗ₜ[ℤ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val := by sorry
