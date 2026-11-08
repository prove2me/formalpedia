-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_product_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0_product_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:08.516633+00:00
-- url     : https://prove2.me/theorems/525834ac-2f81-497d-bdff-15ae059cc6e5
-- title:
--   Tanner Lifted Product: lps Gamma0 product le
-- statement:
--   Original level Np divisibility implies original level N divisibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L148-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L148-L154

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0_product_le (N p : ℕ) :
    CongruenceSubgroup.Gamma0 (N*p) ≤ CongruenceSubgroup.Gamma0 N := by sorry
