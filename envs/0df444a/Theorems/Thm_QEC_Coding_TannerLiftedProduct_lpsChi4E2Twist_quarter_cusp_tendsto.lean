-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_quarter_cusp_tendsto
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_quarter_cusp_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:34.994546+00:00
-- url     : https://prove2.me/theorems/63645b0e-6413-4def-850a-6da1a0b1728e
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Twist quarter cusp tendsto
-- statement:
--   The complete actual cusp vector computes the nonzero quarter-cusp constant minus twelve over Gauss.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L341-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L341-L354

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_quarter_cusp_tendsto :
    Tendsto (lpsChi4E2Twist ∣[(2:ℤ)] lpsE2PrimeCuspMatrix 4) UpperHalfPlane.atImInfty
      (𝓝 (-12/gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))) := by sorry
