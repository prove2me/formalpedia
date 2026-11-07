-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_eq_of_orbit_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_eq_of_orbit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:49.702538+00:00
-- url     : https://prove2.me/theorems/9dd42b46-19fd-466a-8fc4-7fce60104090
-- title:
--   Tanner Lifted Product: lps Original Cusp Width Nat eq of orbit eq
-- statement:
--   The true minimal natural cusp width is independent of the integral orbit representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L84-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L84-L88

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_eq_of_orbit_eq (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2, ℤ)) (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    lpsOriginalCuspWidthNat N ρ = lpsOriginalCuspWidthNat N ρ' := by sorry
