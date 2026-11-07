-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jacobiProd
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jacobiProd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:45.11551+00:00
-- url     : https://prove2.me/theorems/79a5b66b-018c-42cd-a90c-bd2565f8b44b
-- title:
--   Jacobi Cube Product: signed Euler jacobi Prod
-- statement:
--   The Laurent Euler derivation turns the JTP product side into minus
--   the cube of Euler's product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L264-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L264-L276

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jacobiProd :
    signedEuler jacobiProd = -(eulerProduct ^ 3) := by sorry
