-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_coeff_qBinom_eq_coeff_qPochhammerInv
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qBinom_eq_coeff_qPochhammerInv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:41.906816+00:00
-- url     : https://prove2.me/theorems/200eb19c-187b-4232-90f3-fb5e6a12f705
-- title:
--   Formal Power Series: coeff q Binom eq coeff q Pochhammer Inv
-- statement:
--   For `j + k ≤ n`, the `j`-th coefficient of `qBinom n k X` equals that of `qPochhammerInv k`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L138-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L138-L158

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
omit [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.coeff_qBinom_eq_coeff_qPochhammerInv {k j n : ℕ} (hjk : j + k ≤ n) :
    PowerSeries.coeff j (QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom n k (X : R⟦X⟧)) =
    PowerSeries.coeff j (qPochhammerInv (R := R) k) := by sorry
