-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_succ_eq_one_sub_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_succ_eq_one_sub_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:52.182204+00:00
-- url     : https://prove2.me/theorems/25b59a89-5da2-46e4-bcdd-eb2352b25401
-- title:
--   Formal Power Series: q Pochhammer succ eq one sub mul
-- statement:
--   The shift identity `(a; X)_{n+1} = (1 - a) * (aX; X)_n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L69-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L69-L73

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_succ_eq_one_sub_mul (a : R⟦X⟧) (n : ℕ) :
    qPochhammer a (n + 1) = (1 - a) * qPochhammer (a * X) n := by sorry
