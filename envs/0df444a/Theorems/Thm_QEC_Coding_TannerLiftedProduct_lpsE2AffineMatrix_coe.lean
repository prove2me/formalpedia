-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:39.802029+00:00
-- url     : https://prove2.me/theorems/8ee7b456-56ae-4ff0-8495-67cf1515e237
-- title:
--   Tanner Lifted Product: lps E2 Affine Matrix coe
-- statement:
--   The actual affine matrix entries are used by the action and cusp arithmetic proofs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L149-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L149-L150

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_coe (m : ℕ) (hm : 0<m) (r : ℝ) :
    (lpsE2AffineMatrix m hm r:Matrix (Fin 2) (Fin 2) ℝ)=!![(m:ℝ),r;0,1] := by sorry
