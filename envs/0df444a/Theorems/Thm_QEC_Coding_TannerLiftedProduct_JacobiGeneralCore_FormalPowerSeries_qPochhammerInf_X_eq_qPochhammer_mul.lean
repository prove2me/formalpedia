-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_X_eq_qPochhammer_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_X_eq_qPochhammer_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:07.3472+00:00
-- url     : https://prove2.me/theorems/a9fd3f97-bc93-4057-bc51-e98eac9219b7
-- title:
--   Formal Power Series: q Pochhammer Inf X eq q Pochhammer mul
-- statement:
--   `qPochhammerInf X = qPochhammer X n · qPochhammerInf (X * X^n)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSEuler.lean#L58-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSEuler.lean#L58-L60

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_X_eq_qPochhammer_mul (n : ℕ) :
    qPochhammerInf (X : R⟦X⟧) = qPochhammer X n * qPochhammerInf (X * X ^ n) := by sorry
