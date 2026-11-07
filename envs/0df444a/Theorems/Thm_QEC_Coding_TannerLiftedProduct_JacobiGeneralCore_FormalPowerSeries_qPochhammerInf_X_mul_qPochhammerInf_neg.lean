-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_X_mul_qPochhammerInf_neg
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_X_mul_qPochhammerInf_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:10.068871+00:00
-- url     : https://prove2.me/theorems/53b64ce3-0d55-437b-a451-a214c33a740c
-- title:
--   Formal Power Series: q Pochhammer Inf X mul q Pochhammer Inf neg
-- statement:
--   `qPochhammerInf X * qPochhammerInf(-a) = Σ_n X^{C(n,2)} a^n qPochhammerInf(X · X^n)`
--   in `R⟦X⟧`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L402-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L402-L409

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_X_mul_qPochhammerInf_neg (a : R⟦X⟧) :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInf (-a) =
    ∑' n : ℕ, X ^ n.choose 2 * a ^ n * qPochhammerInf (X * X ^ n) := by sorry
