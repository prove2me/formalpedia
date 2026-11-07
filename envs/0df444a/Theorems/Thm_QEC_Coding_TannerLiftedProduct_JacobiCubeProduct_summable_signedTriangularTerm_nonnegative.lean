-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_summable_signedTriangularTerm_nonnegative
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.summable_signedTriangularTerm_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:19.845227+00:00
-- url     : https://prove2.me/theorems/bd4a63ca-7d35-4be4-9fc5-c640700cb9ca
-- title:
--   Jacobi Cube Product: summable signed Triangular Term nonnegative
-- statement:
--   Pairing `z` with `-z-1` turns the bilateral signed triangular series
--   into twice its nonnegative half.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L405-L423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L405-L423

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.summable_signedTriangularTerm_nonnegative :
    Summable (fun n : ℕ => signedTriangularTerm (n : ℤ)) := by sorry
