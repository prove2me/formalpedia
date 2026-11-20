-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_one_lpsThetaHeckePrimePower
-- name    : QEC.Coding.TannerLiftedProduct.coeff_one_lpsThetaHeckePrimePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:26:58.643204+00:00
-- url     : https://prove2.me/theorems/73950e2e-6a39-4604-ae83-21e1e10a5ef3
-- title:
--   Tanner Lifted Product: coeff one lps Theta Hecke Prime Power
-- statement:
--   The original theta prime-power coefficient is recovered by the true operator first coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaHecke.lean#L30-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaHecke.lean#L30-L35

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_one_lpsThetaHeckePrimePower (p : ℕ) (a : LPSResiduePrime p) (r : ℕ) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsThetaHeckePrimePower p a r))=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder a.q a.modFour)) := by sorry
