-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetFractionRoot_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetFractionRoot_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:04:16.280319+00:00
-- url     : https://prove2.me/theorems/c977d059-d8e8-455b-901e-e26f07c6482c
-- title:
--   Tanner Lifted Product: lps Original Coset Fraction Root injective
-- statement:
--   Genuine inverse-coset branch injectivity from faithful localization and the actual proved exact original stabilizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L152-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L152-L175

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetFractionRoot_injective (N : ℕ) (hN : 0<N) :
    Function.Injective (lpsOriginalCosetFractionRoot N hN) := by sorry
