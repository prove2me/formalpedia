-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPair
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:00.618327+00:00
-- url     : https://prove2.me/theorems/e8c7119d-656d-4d49-853d-ca536ae50059
-- title:
--   Jacobi Cube Product: signed Euler jtp Pair
-- statement:
--   The Jacobi Cube Product construction uses the signed Euler jtp Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L641-L683
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L641-L683

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPair (t : ℕ) :
    signedEuler (jtpIntegerTerm ((t : ℤ) + 1)) +
        signedEuler (jtpIntegerTerm (-(t : ℤ))) =
      -signedTriangularTerm (t : ℤ) := by sorry
