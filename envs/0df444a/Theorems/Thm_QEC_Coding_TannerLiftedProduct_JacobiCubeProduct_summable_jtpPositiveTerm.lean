-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_summable_jtpPositiveTerm
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.summable_jtpPositiveTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:40.513423+00:00
-- url     : https://prove2.me/theorems/b9301b44-1c48-47a3-a1a7-ee12eba9c1b1
-- title:
--   Jacobi Cube Product: summable jtp Positive Term
-- statement:
--   The Jacobi Cube Product construction uses the summable jtp Positive Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L501-L514
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L501-L514

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.summable_jtpPositiveTerm : Summable jtpPositiveTerm := by sorry
