-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveGamma0CosetEquiv_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveGamma0CosetEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:04.681323+00:00
-- url     : https://prove2.me/theorems/eb10ba0d-ec1a-44f7-a6b8-ec7e55a6cef8
-- title:
--   Tanner Lifted Product: lps Effective Gamma0 Coset Equiv mk
-- statement:
--   The original/effective Gamma0 quotient equivalence sends actual representatives to their projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L16-L18
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L16-L18

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveGamma0CosetEquiv_mk (N : ℕ) (h : SL(2,ℤ)) :
    lpsEffectiveGamma0CosetEquiv N (QuotientGroup.mk h) =
      QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict h) := by sorry
