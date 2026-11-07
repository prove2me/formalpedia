-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_summable_signedTriangularTerm
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.summable_signedTriangularTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:04.328197+00:00
-- url     : https://prove2.me/theorems/ff1b9333-f882-4fcf-a611-92ecaf6c7897
-- title:
--   Jacobi Cube Product: summable signed Triangular Term
-- statement:
--   The Jacobi Cube Product construction uses the summable signed Triangular Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L298-L310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L298-L310

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.summable_signedTriangularTerm : Summable signedTriangularTerm := by sorry
