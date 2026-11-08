-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlashPetersson_bounded
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlashPetersson_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:56:33.944183+00:00
-- url     : https://prove2.me/theorems/4897362c-459d-4d42-92a8-8405a03c7dec
-- title:
--   Tanner Lifted Product: lps Weight Two Slash Petersson bounded
-- statement:
--   Actual cusp self-bounds and weight-two covariance bound every mixed positive-determinant slash term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L26-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L26-L44

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlashPetersson_bounded (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    ∃C:ℝ,∀τ, ‖petersson 2 (f ∣[(2:ℤ)] A) g τ‖ ≤ C := by sorry
