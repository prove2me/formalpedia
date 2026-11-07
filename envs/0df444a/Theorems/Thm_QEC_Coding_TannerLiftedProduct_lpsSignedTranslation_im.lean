-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_im
-- name    : QEC.Coding.TannerLiftedProduct.lpsSignedTranslation_im
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:45.407102+00:00
-- url     : https://prove2.me/theorems/1e67c584-0069-444c-9350-908ac8be37b3
-- title:
--   Tanner Lifted Product: lps Signed Translation im
-- statement:
--   A genuine signed real translation preserves imaginary height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L95-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L95-L104

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsSignedTranslation_im (g : GL (Fin 2) ℝ) (x : ℝ)
    (hg : g=Matrix.GeneralLinearGroup.upperRightHom x ∨
      g= -Matrix.GeneralLinearGroup.upperRightHom x) (τ : ℍ) :
    (g • τ).im=τ.im := by sorry
