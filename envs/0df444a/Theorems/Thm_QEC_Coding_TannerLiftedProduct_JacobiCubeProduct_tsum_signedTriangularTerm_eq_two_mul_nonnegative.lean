-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_tsum_signedTriangularTerm_eq_two_mul_nonnegative
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.tsum_signedTriangularTerm_eq_two_mul_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:29.515319+00:00
-- url     : https://prove2.me/theorems/f647f79d-d07a-446d-9bde-cd16243f67aa
-- title:
--   Jacobi Cube Product: tsum signed Triangular Term eq two mul nonnegative
-- statement:
--   The Jacobi Cube Product construction uses the tsum signed Triangular Term eq two mul nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L425-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L425-L446

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.tsum_signedTriangularTerm_eq_two_mul_nonnegative :
    (∑' z : ℤ, signedTriangularTerm z) =
      2 * ∑' n : ℕ, signedTriangularTerm (n : ℤ) := by sorry
