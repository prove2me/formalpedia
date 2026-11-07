-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_summable_signedEuler_jtpPositiveShift
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.summable_signedEuler_jtpPositiveShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:09.651691+00:00
-- url     : https://prove2.me/theorems/f1bfca0d-0f3b-4674-8456-ee296c5953bf
-- title:
--   Jacobi Cube Product: summable signed Euler jtp Positive Shift
-- statement:
--   The Jacobi Cube Product construction uses the summable signed Euler jtp Positive Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L691-L705
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L691-L705

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.summable_signedEuler_jtpPositiveShift :
    Summable (fun t : ℕ => signedEuler (jtpPositiveTerm (t + 1))) := by sorry
