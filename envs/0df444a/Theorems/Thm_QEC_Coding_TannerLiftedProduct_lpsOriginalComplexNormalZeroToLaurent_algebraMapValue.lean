-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalZeroToLaurent_algebraMapValue
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalZeroToLaurent_algebraMapValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T06:15:09.189459+00:00
-- url     : https://prove2.me/theorems/d7557536-49e4-406b-ae13-978b1c65a5d3
-- title:
--   Tanner Lifted Product: lps Original Complex Normal Zero To Laurent algebra Map Value
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Complex Normal Zero To Laurent algebra Map Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLaurentNormalizationComparison.lean#L308-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLaurentNormalizationComparison.lean#L308-L309

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
import Mathlib.RingTheory.Localization.BaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local notation "JC" => FractionRing (Polynomial ℂ)
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary001
variable (N : ℕ) (hN : 0 < N)
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary008
local notation "IC0" => integralClosure (Polynomial ℂ) FC
local notation "ICL" => integralClosure (LaurentPolynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary016
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary018
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary024
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary025
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary026
local notation "IZ" => lpsOriginalIntegerNormalZeroChart N hN
local notation "IL" => lpsOriginalIntegerNormalLaurentChart N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary027
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary029
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary030
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary040
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary042
variable [NeZero N]
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary043
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary044
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary046
local notation "TIZ" => ℂ ⊗[ℤ] IZ
local notation "TIL" => ℂ ⊗[ℤ] IL
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary051
attribute [local instance] QEC.Coding.TannerLiftedProduct.laurentNormalizationDictionary052
omit [NeZero N]

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalZeroToLaurent_algebraMapValue (a : IC0) :
    (integralClosure (LaurentPolynomial ℂ) FC).val.toRingHom (algebraMap IC0 ICL a) = a.val := by sorry
