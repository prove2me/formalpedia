-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_not_cuspForm
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_not_cuspForm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:16:47.893682+00:00
-- url     : https://prove2.me/theorems/5cd4b832-7da5-4e69-9c1f-ebf1fcd606d1
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Twist not cusp Form
-- statement:
--   The actual quarter-cusp limit excludes any cusp form with the same underlying function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L364-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L364-L370

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_not_cuspForm :
    ¬∃ f : CuspForm (CongruenceSubgroup.Gamma0 16 : Subgroup (GL (Fin 2) ℝ)) 2,
      (f:ℍ→ℂ)=lpsChi4E2Twist := by sorry
