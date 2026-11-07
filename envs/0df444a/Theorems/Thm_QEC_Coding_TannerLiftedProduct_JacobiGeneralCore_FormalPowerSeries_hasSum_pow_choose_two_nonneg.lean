-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_hasSum_pow_choose_two_nonneg
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.hasSum_pow_choose_two_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:17.527293+00:00
-- url     : https://prove2.me/theorems/72d131a9-698e-42ca-8b02-d0bb3d950bf4
-- title:
--   Formal Power Series: has Sum pow choose two nonneg
-- statement:
--   Cauchy diagonal coefficient for non-negative index `k`: the `(m+k, m)` diagonal of the
--   double series sums to `X^{C(k,2)}` in `R⟦X⟧`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L433-L441
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L433-L441

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.hasSum_pow_choose_two_nonneg (k : ℕ) :
    HasSum (fun m : ℕ =>
      X ^ (m + k).choose 2 * qPochhammerInf (X * X ^ (m + k)) *
      (X ^ m.choose 2 * X ^ m * qPochhammerInv (R := R) m))
      (X ^ k.choose 2 : R⟦X⟧) := by sorry
