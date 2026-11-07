-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPunctInverse_open
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctInverse_open
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:16.301192+00:00
-- url     : https://prove2.me/theorems/9b5255fb-b9a0-4f0e-a4f3-bf75ffe3078f
-- title:
--   Tanner Lifted Product: lps Original Cusp Punct Inverse open
-- statement:
--   The true inverse punctured coordinate is open in the ORIGINAL quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L289-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCusps.lean#L289-L292

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPunctInverse_open (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    IsOpenMap (lpsOriginalCuspPunctInverse N ρ) := by sorry
