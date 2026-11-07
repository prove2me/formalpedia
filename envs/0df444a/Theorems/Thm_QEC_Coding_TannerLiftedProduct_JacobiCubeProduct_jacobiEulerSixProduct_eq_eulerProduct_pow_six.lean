-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiEulerSixProduct_eq_eulerProduct_pow_six
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiEulerSixProduct_eq_eulerProduct_pow_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:27.285202+00:00
-- url     : https://prove2.me/theorems/b10f6c19-427d-48e3-9f7b-8149e8ec176c
-- title:
--   Jacobi Cube Product: jacobi Euler Six Product eq euler Product pow six
-- statement:
--   The Jacobi Cube Product construction uses the jacobi Euler Six Product eq euler Product pow six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L771-L774
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L771-L774

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiEulerSixProduct_eq_eulerProduct_pow_six :
    jacobiEulerSixProduct = eulerProduct ^ 6 := by sorry
