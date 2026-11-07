-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_self_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_self_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:20:21.710244+00:00
-- url     : https://prove2.me/theorems/307a0879-c1c8-47d9-8549-a0ce09f9980d
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Pairing self eq
-- statement:
--   The actual self-pairing is the integral of the nonnegative real square density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L221-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L221-L226

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_self_eq (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f f=(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ : ℝ) := by sorry
