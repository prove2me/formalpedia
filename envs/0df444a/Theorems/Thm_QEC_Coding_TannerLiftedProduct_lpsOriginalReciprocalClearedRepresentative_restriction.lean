-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalClearedRepresentative_restriction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalClearedRepresentative_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:25:38.279781+00:00
-- url     : https://prove2.me/theorems/cc3e6310-e949-4926-af3d-98c8592e58f0
-- title:
--   Tanner Lifted Product: lps Original Reciprocal Cleared Representative restriction
-- statement:
--   The constructed product retains the literal j-power times original restriction germ.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNumerator.lean#L125-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNumerator.lean#L125-L149

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalClearedRepresentative_restriction
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (k : ℕ) :
    let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
    (lpsOriginalFilledMeromorphicRestriction N hN G.val G.property).val =
      (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)^k *
      (lpsOriginalFilledMeromorphicRestriction N hN F hF).val := by sorry
