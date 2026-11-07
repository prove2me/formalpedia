-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_summable_keySummand
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.summable_keySummand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:27.799149+00:00
-- url     : https://prove2.me/theorems/911c3560-295e-46ae-8ce2-d741371228bf
-- title:
--   Formal Power Series: summable key Summand
-- statement:
--   The defining series for `keySum k` is summable in `R⟦X⟧`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L247-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L247-L251

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
omit [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.summable_keySummand (k : ℕ) :
    Summable (fun m : ℕ =>
      X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k)) := by sorry
