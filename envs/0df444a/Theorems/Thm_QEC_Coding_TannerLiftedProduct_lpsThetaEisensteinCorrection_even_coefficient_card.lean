-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinCorrection_even_coefficient_card
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrection_even_coefficient_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:24:42.841825+00:00
-- url     : https://prove2.me/theorems/b1a1a9ab-f4de-4e34-966e-1119a2a2aeda
-- title:
--   Tanner Lifted Product: lps Theta Eisenstein Correction even coefficient card
-- statement:
--   The true correction coefficient times actual PSL cardinality is twice the prime-power divisor sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L177-L199
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L177-L199

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrection_even_coefficient_card (p : ℕ)
    (a : LPSResiduePrime p) (n : ℕ) :
    (Fintype.card PSL(2,ZMod a.q):ℂ)*
      PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
        (lpsThetaEisensteinCorrection a.q (by intro h;have hm:=a.modFour;omega)))=
      2*(∑ i∈Finset.range (2*n+1),(p:ℂ)^i) := by sorry
