-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammer_eq_of_le
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammer_eq_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:33:01.119631+00:00
-- url     : https://prove2.me/theorems/82fb360e-ffd4-49ef-87fb-98ee0718087f
-- title:
--   Formal Power Series: coeff q Pochhammer eq of le
-- statement:
--   For `N ≥ M > d`, the `d`-th coefficient of `(a; X)_N` equals that of `(a; X)_M`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L88-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L88-L95

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammer_eq_of_le (a : R⟦X⟧) {d M N : ℕ}
    (hM : d < M) (hN : M ≤ N) :
    coeff d (qPochhammer a N) = coeff d (qPochhammer a M) := by sorry
