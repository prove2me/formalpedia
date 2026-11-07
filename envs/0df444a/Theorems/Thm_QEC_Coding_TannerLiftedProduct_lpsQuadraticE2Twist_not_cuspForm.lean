-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_not_cuspForm
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_not_cuspForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:01:44.119115+00:00
-- url     : https://prove2.me/theorems/fd11e591-1743-444a-97b7-35136bc1ca11
-- title:
--   Tanner Lifted Product: lps Quadratic E2 Twist not cusp Form
-- statement:
--   The actual nonzero rational-cusp limit excludes a cusp form with the same underlying function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L333-L339
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean#L333-L339

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_not_cuspForm (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    ¬∃ f : CuspForm (CongruenceSubgroup.Gamma0 (q^2) : Subgroup (GL (Fin 2) ℝ)) 2,
      (f:ℍ→ℂ)=lpsQuadraticE2Twist q := by sorry
