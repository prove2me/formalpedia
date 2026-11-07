-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_hasSum_pow_choose_two_neg
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.hasSum_pow_choose_two_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:11.743198+00:00
-- url     : https://prove2.me/theorems/e0ed2a64-2fc3-4a0f-97e8-766e65004ac1
-- title:
--   Formal Power Series: has Sum pow choose two neg
-- statement:
--   Cauchy diagonal coefficient for negative index `-(l+1)`: the `(n, n+l+1)` diagonal of the
--   double series sums to `X^{C(l+2,2)}` in `R⟦X⟧`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L445-L454
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L445-L454

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.hasSum_pow_choose_two_neg (l : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ n.choose 2 * qPochhammerInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) * qPochhammerInv (R := R) (n + (l + 1))))
      (X ^ (l + 2).choose 2 : R⟦X⟧) := by sorry
