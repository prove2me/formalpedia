-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineNomeLimit
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAffineNomeLimit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:03.178755+00:00
-- url     : https://prove2.me/theorems/daa04ad2-e984-4819-b9eb-a9ee3a0e955c
-- title:
--   Tanner Lifted Product: lps Original Affine Nome Limit
-- statement:
--   The actual affine nome tends to zero at imaginary infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L39-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L39-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAffineNomeLimit (m : ℕ) (hm : 0<m) (r : ℝ) :
    Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1
      ((lpsE2AffineMatrix m hm r • τ:ℍ):ℂ))
      UpperHalfPlane.atImInfty (𝓝 0) := by sorry
