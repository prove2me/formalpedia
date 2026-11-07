-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_keySum_sub_keySum_succ
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.keySum_sub_keySum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:52:44.806976+00:00
-- url     : https://prove2.me/theorems/0f41074d-ad2b-4e39-9946-77e5c461e841
-- title:
--   Formal Power Series: key Sum sub key Sum succ
-- statement:
--   The recurrence: `S_k − S_{k+1} = X^{k+1} (S_{k+2} − S_{k+1})`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L316-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L316-L321

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.keySum_sub_keySum_succ (k : ℕ) :
    keySum (R := R) k - keySum (k + 1) =
    X ^ (k + 1) * (keySum (R := R) (k + 2) - keySum (k + 1)) := by sorry
