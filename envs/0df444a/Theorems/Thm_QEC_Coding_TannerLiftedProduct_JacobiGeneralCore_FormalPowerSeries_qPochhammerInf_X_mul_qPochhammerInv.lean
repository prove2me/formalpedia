-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammerInf_X_mul_qPochhammerInv
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_X_mul_qPochhammerInv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:33.507196+00:00
-- url     : https://prove2.me/theorems/b4e488a9-fff8-42eb-aa58-dc60237369b9
-- title:
--   Formal Power Series: q Pochhammer Inf X mul q Pochhammer Inv
-- statement:
--   `qPochhammerInf X * qPochhammerInv n = qPochhammerInf (X * X^n)`: multiplying the infinite
--   product by the `n`-th inverse Pochhammer symbol shifts the argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L89-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L89-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammerInf_X_mul_qPochhammerInv (n : ℕ) :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInv (R := R) n = qPochhammerInf (X * X ^ n) := by sorry
