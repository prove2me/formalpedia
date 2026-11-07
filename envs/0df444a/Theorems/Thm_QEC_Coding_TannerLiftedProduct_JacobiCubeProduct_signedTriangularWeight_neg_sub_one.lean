-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedTriangularWeight_neg_sub_one
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedTriangularWeight_neg_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:19.152068+00:00
-- url     : https://prove2.me/theorems/066f32a5-11ac-4005-bec3-c86af2b959f5
-- title:
--   Jacobi Cube Product: signed Triangular Weight neg sub one
-- statement:
--   The Jacobi Cube Product construction uses the signed Triangular Weight neg sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L353-L366
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L353-L366

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedTriangularWeight_neg_sub_one (z : ℤ) :
    jacobiParitySign (-z - 1) * (2 * ((-z - 1 : ℤ) : ℚ) + 1) =
      jacobiParitySign z * (2 * (z : ℚ) + 1) := by sorry
