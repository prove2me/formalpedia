-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicDeltaQCoefficient_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicDeltaQCoefficient_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:32:37.858452+00:00
-- url     : https://prove2.me/theorems/cda9909f-5544-49f4-b32a-0666790297dd
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Delta QCoefficient analytic
-- statement:
--   The genuine Delta quotient by its q-zero is analytic at zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L88-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicModularRatio.lean#L88-L93

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicDeltaQCoefficient_analytic :
    AnalyticAt ℂ lpsOriginalMeromorphicDeltaQCoefficient 0 := by sorry
