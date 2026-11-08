-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoSlashPetersson_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlashPetersson_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:57:00.62718+00:00
-- url     : https://prove2.me/theorems/b4c60055-b343-4220-a2fa-343963c91fec
-- title:
--   Tanner Lifted Product: lps Weight Two Slash Petersson integrable
-- statement:
--   Every actual mixed slash term is absolutely integrable on the proved finite Gamma0 domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L47-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L47-L56

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlashPetersson_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    IntegrableOn (petersson 2 (f ∣[(2:ℤ)] A) g) (lpsGamma0PeterssonDomain N) volume := by sorry
