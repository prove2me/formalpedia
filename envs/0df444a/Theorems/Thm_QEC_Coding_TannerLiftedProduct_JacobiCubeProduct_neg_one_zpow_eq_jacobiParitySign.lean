-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_neg_one_zpow_eq_jacobiParitySign
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.neg_one_zpow_eq_jacobiParitySign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:51.053445+00:00
-- url     : https://prove2.me/theorems/eb2b50a4-ad03-425e-b609-0a5df3532a12
-- title:
--   Jacobi Cube Product: neg one zpow eq jacobi Parity Sign
-- statement:
--   The Jacobi Cube Product construction uses the neg one zpow eq jacobi Parity Sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L278-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L278-L281

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.neg_one_zpow_eq_jacobiParitySign (z : ℤ) :
    ((-1 : ℚ) ^ z) = jacobiParitySign z := by sorry
