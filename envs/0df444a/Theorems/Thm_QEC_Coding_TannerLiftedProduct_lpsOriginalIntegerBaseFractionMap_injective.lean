-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerBaseFractionMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerBaseFractionMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:15:53.407917+00:00
-- url     : https://prove2.me/theorems/c15d0d53-f23e-4a3a-8ba1-29f258b6bb60
-- title:
--   Tanner Lifted Product: lps Original Integer Base Fraction Map injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Base Fraction Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L388-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean#L388-L391

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerBaseFractionMap_injective :
    Function.Injective lpsOriginalIntegerBaseFractionMap := by sorry
