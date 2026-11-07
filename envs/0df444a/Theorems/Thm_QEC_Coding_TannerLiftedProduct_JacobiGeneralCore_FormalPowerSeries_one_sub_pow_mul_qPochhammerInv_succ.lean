-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_one_sub_pow_mul_qPochhammerInv_succ
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.one_sub_pow_mul_qPochhammerInv_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:49.600209+00:00
-- url     : https://prove2.me/theorems/eb17a062-71e4-4324-92b7-68affdc9ca0d
-- title:
--   Formal Power Series: one sub pow mul q Pochhammer Inv succ
-- statement:
--   The recursion `(1 - X^{k+1}) * qPochhammerInv(k+1) = qPochhammerInv(k)` for the inverse
--   q-Pochhammer symbol.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L61-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L61-L66

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

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.one_sub_pow_mul_qPochhammerInv_succ (k : ℕ) :
    (1 - (X : R⟦X⟧) ^ (k + 1)) * qPochhammerInv (R := R) (k + 1) = qPochhammerInv k := by sorry
