-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_euler_second_identity
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.euler_second_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:39.156932+00:00
-- url     : https://prove2.me/theorems/eb84e947-cc5a-4079-a514-97be1308d106
-- title:
--   Formal Power Series: euler second identity
-- statement:
--   FPS Euler second identity: `qPochhammerInf(-a) = Σ_{k≥0} X^{C(k,2)} · a^k · (qPochhammer X k)⁻¹`
--   in `R⟦X⟧`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L196-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L196-L209

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.euler_second_identity (a : R⟦X⟧) :
    qPochhammerInf (-a) = ∑' k : ℕ, X ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k := by sorry
