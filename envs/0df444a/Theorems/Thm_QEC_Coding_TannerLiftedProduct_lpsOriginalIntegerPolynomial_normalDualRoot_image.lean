-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_normalDualRoot_image
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_normalDualRoot_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:59:04.377173+00:00
-- url     : https://prove2.me/theorems/1c8423c7-7cfc-48ab-99f8-2b3e075f0b13
-- title:
--   Tanner Lifted Product: lps Original Integer Polynomial normal Dual Root image
-- statement:
--   transport the proved dual equation through any actual normalization map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L108-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L108-L125

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_normalDualRoot_image
    (N : ℕ) [NeZero N] (hN : 0 < N)
    (K : Type*) [CommRing K]
    (f : lpsOriginalIntegerNormalZeroChart N hN →+* K) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom K)
        (f (lpsOriginalIntegerNormalJN N hN)))
      (f (lpsOriginalIntegerNormalJ N hN)) = 0 := by sorry
