-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jacobiBilateral
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jacobiBilateral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:08.795412+00:00
-- url     : https://prove2.me/theorems/b9113e75-1134-4ad6-8bbe-e2a9f70038ec
-- title:
--   Jacobi Cube Product: signed Euler jacobi Bilateral
-- statement:
--   The series side of differentiated JTP is minus Jacobi's signed
--   triangular-number series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L751-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L751-L761

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jacobiBilateral :
    signedEuler jacobiBilateral = -jacobiSignedCubeSeries := by sorry
