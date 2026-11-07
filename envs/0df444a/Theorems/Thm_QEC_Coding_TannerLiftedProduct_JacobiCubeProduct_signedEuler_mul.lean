-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:21.555543+00:00
-- url     : https://prove2.me/theorems/a4b163a1-87ce-47d0-b270-011cfed065ce
-- title:
--   Jacobi Cube Product: signed Euler mul
-- statement:
--   The Jacobi Cube Product construction uses the signed Euler mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L116-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L116-L126

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_mul (F G : Bivariate) :
    signedEuler (F * G) =
      evalNegOneSeries F * signedEuler G +
        signedEuler F * evalNegOneSeries G := by sorry
