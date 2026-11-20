-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_scaled_memIntegralLattice
-- name    : QEC.Coding.TannerLiftedProduct.lpsTheta_scaled_memIntegralLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:42:30.157234+00:00
-- url     : https://prove2.me/theorems/6cbae9d8-133a-44db-b64d-8e531feb0efd
-- title:
--   Tanner Lifted Product: lps Theta scaled mem Integral Lattice
-- statement:
--   The scaled ORIGINAL theta cusp remainder is in the actual all-integer cusp lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L111-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean#L111-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsTheta_scaled_memIntegralLattice (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaIntegerDenominator q • lpsThetaCuspidalRemainder q hq4 ∈
      lpsIntegralCuspLattice ((4*q)^2) := by sorry
