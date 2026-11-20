-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspidalRemainder_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainder_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:23:40.24643+00:00
-- url     : https://prove2.me/theorems/c82e082e-e66a-4ee2-a71e-9d7b71b38742
-- title:
--   Tanner Lifted Product: lps Theta Cuspidal Remainder apply
-- statement:
--   The bundled CuspForm retains the actual theta minus correction function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L138-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L138-L140

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainder_apply (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (z : ℍ) :
    lpsThetaCuspidalRemainder q hq4 z=lpsStandardTheta q z-
      lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4) z := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.lpsThetaCuspidalRemainder_apply
