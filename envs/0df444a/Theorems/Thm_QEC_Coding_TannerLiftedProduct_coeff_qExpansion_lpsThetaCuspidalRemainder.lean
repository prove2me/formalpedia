-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaCuspidalRemainder
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaCuspidalRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:25:41.378848+00:00
-- url     : https://prove2.me/theorems/eb04e03f-7d4c-4d62-a6ef-f1522f084578
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Theta Cuspidal Remainder
-- statement:
--   Every genuine cuspidal coefficient is the representation count minus the full correction coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L143-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L143-L156

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaCuspidalRemainder (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))=
      ((PowerSeries.coeff n (lpsTraceThetaSeries q):ℕ):ℂ)-lpsThetaEisensteinCorrectionCoefficient q n := by sorry
