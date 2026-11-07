-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammer_succ
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammer_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:32:49.593814+00:00
-- url     : https://prove2.me/theorems/3a800ef2-5e44-45f1-8b14-035ca0ea2e66
-- title:
--   Formal Power Series: coeff q Pochhammer succ
-- statement:
--   For `d < n`, the `d`-th coefficient of `(a; X)_{n+1}` equals that of `(a; X)_n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L82-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L82-L85

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPS
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammer_succ (a : R⟦X⟧) {d n : ℕ} (hdn : d < n) :
    coeff d (qPochhammer a (n + 1)) = coeff d (qPochhammer a n) := by sorry
