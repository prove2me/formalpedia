-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:06.205205+00:00
-- url     : https://prove2.me/theorems/8c553486-451b-471f-908d-9f79837f9bdc
-- title:
--   Jacobi Cube Product: signed Euler jtp Positive Term
-- statement:
--   The Jacobi Cube Product construction uses the signed Euler jtp Positive Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L685-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L685-L689

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm (n : ℕ) :
    signedEuler (jtpPositiveTerm n) =
      PowerSeries.C (((n : ℤ) : ℚ) * ((-1 : ℚ) ^ (n : ℤ))) *
        PowerSeries.X ^ n.choose 2 := by sorry
