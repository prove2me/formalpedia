-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiSignedCubeSeries_eq_eulerProduct_cube
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_eq_eulerProduct_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:26.958049+00:00
-- url     : https://prove2.me/theorems/3baca167-3ceb-4c2a-bb54-bdbebc9f1468
-- title:
--   Jacobi Cube Product: jacobi Signed Cube Series eq euler Product cube
-- statement:
--   Jacobi's signed triangular-number series is Euler's product cubed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L764-L769
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L764-L769

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_eq_eulerProduct_cube :
    jacobiSignedCubeSeries = eulerProduct ^ 3 := by sorry
