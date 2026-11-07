-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_add_right
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:19.031685+00:00
-- url     : https://prove2.me/theorems/e37edf9d-001b-4de4-a139-1398a926e01b
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Pairing add right
-- statement:
--   Absolute convergence gives additivity of the actual integral in its second argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L348-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L348-L353

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_add_right (N : ℕ) [NeZero N]
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f (g+h)=
      lpsCuspPeterssonPairing N f g+lpsCuspPeterssonPairing N f h := by sorry
