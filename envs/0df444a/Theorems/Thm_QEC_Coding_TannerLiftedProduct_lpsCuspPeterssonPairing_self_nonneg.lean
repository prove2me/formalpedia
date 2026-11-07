-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_self_nonneg
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_self_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:21:31.509062+00:00
-- url     : https://prove2.me/theorems/3105d0b4-5703-4660-86e4-e451137e8a45
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Pairing self nonneg
-- statement:
--   The actual convergent self-pairing is nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L229-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L229-L233

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_self_nonneg (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    0≤(lpsCuspPeterssonPairing N f f).re := by sorry
