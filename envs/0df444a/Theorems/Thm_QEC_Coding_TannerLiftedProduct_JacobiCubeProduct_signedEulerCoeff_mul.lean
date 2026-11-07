-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEulerCoeff_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEulerCoeff_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:20.522179+00:00
-- url     : https://prove2.me/theorems/b1e5926a-36b5-48e7-9d21-d8cc45e5dcf5
-- title:
--   Jacobi Cube Product: signed Euler Coeff mul
-- statement:
--   The Jacobi Cube Product construction uses the signed Euler Coeff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L91-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L91-L114

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEulerCoeff_mul (f g : LaurentQ) :
    signedEulerCoeff (f * g) =
      evalNegOne f * signedEulerCoeff g +
        signedEulerCoeff f * evalNegOne g := by sorry
