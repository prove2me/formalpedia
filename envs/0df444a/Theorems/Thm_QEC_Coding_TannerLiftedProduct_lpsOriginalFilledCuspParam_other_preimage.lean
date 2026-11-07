-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_other_preimage
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_other_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:39.714742+00:00
-- url     : https://prove2.me/theorems/317f3862-608f-47f4-bad6-5bd11fc4fe55
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Param other preimage
-- statement:
--   The filled parametrization of a different actual cusp misses the given cusp-chart image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L355-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L355-L367

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspParam_other_preimage (N : ℕ) [NeZero N]
    (c d : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (hd : d≠c)
    (s : Set ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)) :
    lpsOriginalFilledCuspParam N d ⁻¹' (lpsOriginalFilledCuspParam N c '' s)=∅ := by sorry
