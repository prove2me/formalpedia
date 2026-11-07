-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilationCuspE4_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspE4_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:19.892378+00:00
-- url     : https://prove2.me/theorems/ef430a75-6d7b-4c6f-a69d-5ff9217d9837
-- title:
--   Tanner Lifted Product: lps Original JDilation Cusp E4 analytic
-- statement:
--   Analyticity of the actual translated E4 cusp coefficient at zero from its proved positive strict period and bundled cusp boundedness; used by the meromorphic ratio.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L195-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L195-L200

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspE4_analytic (N : ℕ) [NeZero N] (hN : 0<N) (ρ : SL(2,ℤ)) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction (lpsOriginalCuspGroup N ρ).strictWidthInfty
      (lpsOriginalJDilationCuspE4 N hN ρ)) 0 := by sorry
