-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_dvd_of_orbit_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_of_orbit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:47.021513+00:00
-- url     : https://prove2.me/theorems/fa4b187b-218f-48f1-9b8a-2aab20346271
-- title:
--   Tanner Lifted Product: lps Original Cusp Width Nat dvd of orbit eq
-- statement:
--   Actual period transport makes one genuine positive minimal cusp width divide the other.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L72-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L72-L81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_dvd_of_orbit_eq (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2, ℤ)) (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    lpsOriginalCuspWidthNat N ρ ∣ lpsOriginalCuspWidthNat N ρ' := by sorry
