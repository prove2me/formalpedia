-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_add_left
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_add_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:11.598482+00:00
-- url     : https://prove2.me/theorems/654effba-bb66-4e9c-b5af-e67a5c17fcf9
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Pairing add left
-- statement:
--   The actual convergent pairing is additive in its first argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L494-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L494-L502

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_add_left (N : ℕ) [NeZero N]
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (f+g) h=
      lpsCuspPeterssonPairing N f h+lpsCuspPeterssonPairing N g h := by sorry
