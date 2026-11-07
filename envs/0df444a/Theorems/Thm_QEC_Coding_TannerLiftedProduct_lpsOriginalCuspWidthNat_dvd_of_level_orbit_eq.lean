-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_dvd_of_level_orbit_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_of_level_orbit_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:30:46.819677+00:00
-- url     : https://prove2.me/theorems/5261f797-eab7-42fa-9742-308af1b11576
-- title:
--   Tanner Lifted Product: lps Original Cusp Width Nat dvd of level orbit eq
-- statement:
--   Changing a genuine lower-level representative preserves actual higher-level width divisibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L91-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L91-L96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_of_level_orbit_eq (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N ∣ M) (ρ ρ' : SL(2, ℤ))
    (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    lpsOriginalCuspWidthNat N ρ ∣ lpsOriginalCuspWidthNat M ρ' := by sorry
