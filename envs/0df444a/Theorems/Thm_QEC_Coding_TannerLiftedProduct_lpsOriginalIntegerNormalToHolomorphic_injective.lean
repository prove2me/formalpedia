-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalToHolomorphic_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalToHolomorphic_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:00:42.737392+00:00
-- url     : https://prove2.me/theorems/0221fc66-4160-4bda-836f-b319d0919683
-- title:
--   Tanner Lifted Product: lps Original Integer Normal To Holomorphic injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal To Holomorphic injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L150-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L150-L155

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalToHolomorphic_injective (N : ℕ) (hN : 0 < N) :
    Function.Injective (lpsOriginalIntegerNormalToHolomorphic N hN) := by sorry
