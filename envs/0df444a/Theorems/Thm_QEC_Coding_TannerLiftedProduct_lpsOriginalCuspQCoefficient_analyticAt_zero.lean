-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspQCoefficient_analyticAt_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_analyticAt_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:43:08.935909+00:00
-- url     : https://prove2.me/theorems/25dd390e-a65d-4ecc-8d55-847c222b13bc
-- title:
--   Tanner Lifted Product: lps Original Cusp QCoefficient analytic At zero
-- statement:
--   Genuine cusp vanishing proves analyticity at zero in the actual minimal-width coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspQDifferential.lean#L28-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspQDifferential.lean#L28-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspQCoefficient_analyticAt_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) : AnalyticAt ℂ (lpsOriginalCuspQCoefficient N f ρ) 0 := by sorry
