-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_slash
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_slash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:00:56.562197+00:00
-- url     : https://prove2.me/theorems/16fe0668-ced0-40a7-97ed-120292225c45
-- title:
--   Tanner Lifted Product: lps E2 Affine Matrix slash
-- statement:
--   The true weight-two slash equals the affine E2 function times its determinant m.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L159-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L159-L164

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_slash (m : ℕ) (hm : 0<m) (r : ℝ) :
    (EisensteinSeries.E2 ∣[(2:ℤ)] lpsE2AffineMatrix m hm r)=
      (fun z : ℍ => (m:ℂ)*EisensteinSeries.E2 (lpsE2AffineMatrix m hm r • z)) := by sorry
