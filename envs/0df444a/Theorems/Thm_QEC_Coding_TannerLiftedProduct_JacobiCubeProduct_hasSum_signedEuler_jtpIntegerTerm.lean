-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_hasSum_signedEuler_jtpIntegerTerm
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.hasSum_signedEuler_jtpIntegerTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:35.728242+00:00
-- url     : https://prove2.me/theorems/c78604bc-9bb4-4413-8995-fd42aeedd8a8
-- title:
--   Jacobi Cube Product: has Sum signed Euler jtp Integer Term
-- statement:
--   Apply the Laurent Euler derivation termwise to the general JTP series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L581-L588
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L581-L588

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.hasSum_signedEuler_jtpIntegerTerm :
    letI : TopologicalSpace LaurentQ := ⊥
    HasSum (fun z : ℤ => signedEuler (jtpIntegerTerm z))
      (signedEuler jacobiBilateral) := by sorry
