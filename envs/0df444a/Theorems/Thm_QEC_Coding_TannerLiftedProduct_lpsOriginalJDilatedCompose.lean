-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilatedCompose
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedCompose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:25.469208+00:00
-- url     : https://prove2.me/theorems/5afc29a6-275f-44d1-883b-e1c2afd06561
-- title:
--   Tanner Lifted Product: lps Original JDilated Compose
-- statement:
--   Composition of the SAME original dilated j with level dilation equals the actual square-level dilation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L228-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L228-L235

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilatedCompose (N : ℕ) (hN : 0<N) (σ : ℍ) :
    lpsOriginalJDilated N hN (lpsE2AffineMatrix N hN 0 • σ)=
      lpsOriginalJDilated (N^2) (pow_pos hN 2) σ := by sorry
