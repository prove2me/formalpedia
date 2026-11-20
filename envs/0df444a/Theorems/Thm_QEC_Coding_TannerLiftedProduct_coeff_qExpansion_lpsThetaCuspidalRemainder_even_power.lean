-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaCuspidalRemainder_even_power
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaCuspidalRemainder_even_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:26:24.616585+00:00
-- url     : https://prove2.me/theorems/b7d9079f-4971-493a-b52b-398386b842fe
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Theta Cuspidal Remainder even power
-- statement:
--   The actual even-power coefficient subtracts exactly twice the divisor sum divided by PSL cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L165-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L165-L174

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaCuspidalRemainder_even_power (p q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hp : Odd p) (hpq : ¬q∣p) (n : ℕ) :
    PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))=
      ((PowerSeries.coeff (p^(2*n)) (lpsTraceThetaSeries q):ℕ):ℂ)-
        4*(ArithmeticFunction.sigma 1 (p^(2*n)):ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by sorry
