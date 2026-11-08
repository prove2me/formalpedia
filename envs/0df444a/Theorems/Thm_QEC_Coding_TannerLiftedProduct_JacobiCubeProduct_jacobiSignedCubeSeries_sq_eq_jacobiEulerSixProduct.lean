-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiSignedCubeSeries_sq_eq_jacobiEulerSixProduct
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_sq_eq_jacobiEulerSixProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:15.168028+00:00
-- url     : https://prove2.me/theorems/a0c3180c-3be5-4522-9be3-baf409dc8ec1
-- title:
--   Jacobi Cube Product: jacobi Signed Cube Series sq eq jacobi Euler Six Product
-- statement:
--   The exact cube-product input used by the four-square proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L777-L781
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L777-L781

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiSignedCubeSeries_sq_eq_jacobiEulerSixProduct :
    jacobiSignedCubeSeries ^ 2 = jacobiEulerSixProduct := by sorry
