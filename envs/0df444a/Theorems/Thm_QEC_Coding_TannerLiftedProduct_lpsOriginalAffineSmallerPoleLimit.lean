-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineSmallerPoleLimit
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAffineSmallerPoleLimit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:07.091215+00:00
-- url     : https://prove2.me/theorems/55949832-9cbd-4511-b40c-b0e0d9b02249
-- title:
--   Tanner Lifted Product: lps Original Affine Smaller Pole Limit
-- statement:
--   A genuinely smaller affine pole tends to zero after multiplication by the larger nome power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L68-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L68-L84

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAffineSmallerPoleLimit (m k : ℕ) (hm : 0<m)
    (hmk : m<k) (r : ℝ) :
    Tendsto (fun τ : ℍ=>Function.Periodic.qParam 1 (τ:ℂ)^k*
      lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ))
      UpperHalfPlane.atImInfty (𝓝 0) := by sorry
