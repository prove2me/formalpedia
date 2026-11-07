-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_map_C
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_map_C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:36:35.344784+00:00
-- url     : https://prove2.me/theorems/feff9391-e322-4932-99bf-f8ae85f16a5d
-- title:
--   Jacobi Cube Product: signed Euler map C
-- statement:
--   The Jacobi Cube Product construction uses the signed Euler map C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L128-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L128-L131

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_map_C (g : PowerSeries ℚ) :
    signedEuler (PowerSeries.map (LaurentPolynomial.C (R := ℚ)) g) = 0 := by sorry
