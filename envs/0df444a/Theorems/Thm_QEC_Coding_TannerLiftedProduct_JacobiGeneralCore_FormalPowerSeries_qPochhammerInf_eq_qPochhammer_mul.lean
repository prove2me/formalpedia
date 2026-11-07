-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_eq_qPochhammer_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_eq_qPochhammer_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:38.715338+00:00
-- url     : https://prove2.me/theorems/d6a965e8-39ec-4441-bd66-1531bf9c2e31
-- title:
--   Formal Power Series: q Pochhammer Inf eq q Pochhammer mul
-- statement:
--   `qPochhammerInf a = qPochhammer a n · qPochhammerInf (a · X^n)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSEuler.lean#L47-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSEuler.lean#L47-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_eq_qPochhammer_mul (a : R⟦X⟧) (n : ℕ) :
    qPochhammerInf a = qPochhammer a n * qPochhammerInf (a * X ^ n) := by sorry
