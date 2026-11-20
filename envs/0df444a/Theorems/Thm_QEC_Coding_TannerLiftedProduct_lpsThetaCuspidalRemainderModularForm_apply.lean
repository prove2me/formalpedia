-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspidalRemainderModularForm_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainderModularForm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:23:07.891365+00:00
-- url     : https://prove2.me/theorems/45a6bf86-8120-475d-86a5-3cc32a986229
-- title:
--   Tanner Lifted Product: lps Theta Cuspidal Remainder Modular Form apply
-- statement:
--   The modular remainder is the pointwise difference of the two genuine functions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L112-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L112-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainderModularForm_apply (q : ℕ) [Fact q.Prime]
    (hq2 : q≠2) (z : ℍ) : lpsThetaCuspidalRemainderModularForm q hq2 z=
      lpsStandardTheta q z-lpsThetaEisensteinCorrection q hq2 z := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainderModularForm_apply
