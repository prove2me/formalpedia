-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_norm_sq_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_norm_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:33.828929+00:00
-- url     : https://prove2.me/theorems/6605eb95-b64d-4210-8b07-e71bcd73730b
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Pairing norm sq le
-- statement:
--   Squared Cauchy-Schwarz for the actual convergent Petersson pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonPositive.lean#L93-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonPositive.lean#L93-L102

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Defs
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_norm_sq_le (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ‖lpsCuspPeterssonPairing N f g‖^2 ≤
      (lpsCuspPeterssonPairing N f f).re*(lpsCuspPeterssonPairing N g g).re := by sorry
