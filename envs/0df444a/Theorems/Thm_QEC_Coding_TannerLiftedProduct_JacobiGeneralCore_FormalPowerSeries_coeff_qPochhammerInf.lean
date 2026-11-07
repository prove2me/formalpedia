-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qPochhammerInf
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammerInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:32:30.513209+00:00
-- url     : https://prove2.me/theorems/43b3e1b3-3c4f-47b2-98ab-a49a75fac788
-- title:
--   Formal Power Series: coeff q Pochhammer Inf
-- statement:
--   The `d`-th coefficient of `(a; X)_∞` equals the `d`-th coefficient of `(a; X)_{d+1}`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L122-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPS.lean#L122-L130

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
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qPochhammerInf (a : R⟦X⟧) (d : ℕ) :
    coeff d (qPochhammerInf a) = coeff d (qPochhammer a (d + 1)) := by sorry
