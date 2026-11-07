-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv_tmulValue
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv_tmulValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:59:43.097195+00:00
-- url     : https://prove2.me/theorems/ef52a75f-af83-4903-aa5b-b39218b99d47
-- title:
--   Tanner Lifted Product: lps Original Integer Infinity Normalization Rational Tensor Alg Equiv tmul Value
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Infinity Normalization Rational Tensor Alg Equiv tmul Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNormalizationComparison.lean#L530-L533
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNormalizationComparison.lean#L530-L533

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary030
variable (N : ℕ) (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "BP" => ℚ ⊗[ℤ] Polynomial ℤ
local notation "TB" => ℚ ⊗[ℤ] FQ
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.reciprocalNormalizationDictionary040

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv_tmulValue
    (q : ℚ) (x : integralClosure (Polynomial ℤ) FQ) :
    (lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv N hN (q ⊗ₜ[ℤ] x)).val =
      q • x.val := by sorry
