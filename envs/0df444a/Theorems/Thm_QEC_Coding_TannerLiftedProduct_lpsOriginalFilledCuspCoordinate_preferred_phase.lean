-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspCoordinate_preferred_phase
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspCoordinate_preferred_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:51.075584+00:00
-- url     : https://prove2.me/theorems/51310be6-9f85-4da5-9c5b-6764a8c5d5bc
-- title:
--   Tanner Lifted Product: lps Original Filled Cusp Coordinate preferred phase
-- statement:
--   The actual preferred chart differs by a proved unit-modulus phase on the full cusp source.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L145-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelMapGeometry.lean#L145-L220

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCuspCoordinate_preferred_phase
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    letI := lpsOriginalFilledTopology N
    let c := lpsOriginalCuspOrbit N ρ
    ∃ α : ℂ, α ≠ 0 ∧ ‖α‖ = 1 ∧ ∀ y : LPSOriginalFilledCurve N,
      y ∈ (lpsOriginalFilledCuspPartialEquiv N ρ).source →
      y ∈ (lpsOriginalFilledCuspChart N c).source ∧
      lpsOriginalFilledCuspChart N c y =
        α * lpsOriginalFilledCuspPartialEquiv N ρ y := by sorry
