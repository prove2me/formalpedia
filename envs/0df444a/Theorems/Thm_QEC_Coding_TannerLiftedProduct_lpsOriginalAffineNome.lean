-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineNome
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAffineNome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:08:26.555193+00:00
-- url     : https://prove2.me/theorems/353606c8-5f2a-4112-82db-322c34b9ce6d
-- title:
--   Tanner Lifted Product: lps Original Affine Nome
-- statement:
--   Actual nome of a positive integral affine transform, with the genuine exponential phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L29-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L29-L36

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAffineNome (m : ℕ) (hm : 0<m) (r : ℝ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm r • τ : ℍ) : ℂ)=
      Function.Periodic.qParam 1 (τ:ℂ)^m*Function.Periodic.qParam 1 (r:ℂ) := by sorry
