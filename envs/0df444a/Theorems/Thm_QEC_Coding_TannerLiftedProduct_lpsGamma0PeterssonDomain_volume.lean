-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_volume
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:30.226241+00:00
-- url     : https://prove2.me/theorems/86422421-3da3-4cdd-8122-8cd502233e88
-- title:
--   Tanner Lifted Product: lps Gamma0 Petersson Domain volume
-- statement:
--   The original Gamma0 domain volume uses the exact original integral congruence index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L145-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L145-L149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_volume (N : ℕ) [NeZero N] :
    (volume : Measure ℍ) (lpsGamma0PeterssonDomain N) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * volume ModularGroup.fd := by sorry
