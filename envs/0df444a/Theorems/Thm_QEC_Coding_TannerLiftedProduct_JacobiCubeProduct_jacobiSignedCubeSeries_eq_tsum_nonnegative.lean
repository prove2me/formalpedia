-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiSignedCubeSeries_eq_tsum_nonnegative
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_eq_tsum_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:10.759978+00:00
-- url     : https://prove2.me/theorems/b179de48-5739-41f1-a9a5-a735d568d687
-- title:
--   Jacobi Cube Product: jacobi Signed Cube Series eq tsum nonnegative
-- statement:
--   The Jacobi Cube Product construction uses the jacobi Signed Cube Series eq tsum nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L448-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L448-L456

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_eq_tsum_nonnegative :
    jacobiSignedCubeSeries =
      ∑' n : ℕ, signedTriangularTerm (n : ℤ) := by sorry
