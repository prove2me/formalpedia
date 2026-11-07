-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2SLInverse_real_matrix
-- name    : QEC.Coding.TannerLiftedProduct.lpsE2SLInverse_real_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:03.455624+00:00
-- url     : https://prove2.me/theorems/c9a8dc49-35a1-498e-81fd-772f77b3c746
-- title:
--   Tanner Lifted Product: lps E2 SLInverse real matrix
-- statement:
--   The genuine inverse map has the signed integral adjugate entries used in the actual triangular factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L26-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean#L26-L34

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsE2SLInverse_real_matrix (δ : SL(2,ℤ)) :
    (((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(δ 1 1:ℝ),-(δ 0 1:ℝ);-(δ 1 0:ℝ),(δ 0 0:ℝ)] := by sorry
