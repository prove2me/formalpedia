-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_constantCoeff_qPochhammer_X
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.constantCoeff_qPochhammer_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:34.686206+00:00
-- url     : https://prove2.me/theorems/8b4b0927-2fb3-4d6f-ba5f-b47175f010f7
-- title:
--   Formal Power Series: constant Coeff q Pochhammer X
-- statement:
--   The constant term of `qPochhammer X n` is 1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSEuler.lean#L32-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSEuler.lean#L32-L38

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
omit [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.constantCoeff_qPochhammer_X (n : ℕ) :
    constantCoeff (qPochhammer (X : R⟦X⟧) n) = 1 := by sorry
