-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiSignedCubeSeries_eq_tsum_signedTriangularTerm
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_eq_tsum_signedTriangularTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:44.563233+00:00
-- url     : https://prove2.me/theorems/7eb08438-b958-4d7a-8acd-2bc5f25f633b
-- title:
--   Jacobi Cube Product: jacobi Signed Cube Series eq tsum signed Triangular Term
-- statement:
--   The coefficient-fibre definition of the signed cube series is the
--   normalized bilateral sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L314-L343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L314-L343

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_eq_tsum_signedTriangularTerm :
    jacobiSignedCubeSeries =
      PowerSeries.C (1 / 2 : ℚ) *
        ∑' z : ℤ, signedTriangularTerm z := by sorry
