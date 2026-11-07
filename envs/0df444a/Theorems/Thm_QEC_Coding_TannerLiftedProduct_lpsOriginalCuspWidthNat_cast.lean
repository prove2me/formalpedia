-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_cast
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:02:54.867644+00:00
-- url     : https://prove2.me/theorems/cec027fb-20c7-4624-8ac2-58ea4424177b
-- title:
--   Tanner Lifted Product: lps Original Cusp Width Nat cast
-- statement:
--   Exact equality between this natural width and the actual real minimal strict width; used to identify original cusp coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L195-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L195-L197

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspWidthNat_cast (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).strictWidthInfty=(lpsOriginalCuspWidthNat N ρ:ℝ) := by sorry
