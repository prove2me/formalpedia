-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_succ
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:32:18.118374+00:00
-- url     : https://prove2.me/theorems/533503bd-ee3d-485c-971e-91a94f56b42f
-- title:
--   Formal Power Series: q Pochhammer succ
-- statement:
--   The recurrence `(a; X)_{n+1} = (a; X)_n * (1 - a X^n)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L64-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L64-L66

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_succ (a : R⟦X⟧) (n : ℕ) :
    qPochhammer a (n + 1) = qPochhammer a n * (1 - a * X ^ n) := by sorry
