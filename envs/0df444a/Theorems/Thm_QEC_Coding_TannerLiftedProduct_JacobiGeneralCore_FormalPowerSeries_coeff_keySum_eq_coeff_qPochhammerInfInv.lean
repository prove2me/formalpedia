-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_keySum_eq_coeff_qPochhammerInfInv
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_keySum_eq_coeff_qPochhammerInfInv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:57.627299+00:00
-- url     : https://prove2.me/theorems/73174cf6-20f2-4bf6-8a7f-ecd34843626c
-- title:
--   Formal Power Series: coeff key Sum eq coeff q Pochhammer Inf Inv
-- statement:
--   For `d < k`, the `d`-th coefficient of `keySum k` equals the `d`-th coefficient
--   of `qPochhammerInfInv`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L382-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L382-L387

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_keySum_eq_coeff_qPochhammerInfInv (k : ℕ) (d : ℕ) (hkd : d < k) :
    PowerSeries.coeff d (keySum (R := R) k) = PowerSeries.coeff d (qPochhammerInfInv (R := R)) := by sorry
