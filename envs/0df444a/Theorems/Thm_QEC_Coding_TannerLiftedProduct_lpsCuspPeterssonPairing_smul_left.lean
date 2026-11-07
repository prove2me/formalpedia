-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_smul_left
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_smul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:23.472218+00:00
-- url     : https://prove2.me/theorems/800eeb71-1897-4158-b9cd-6b7fed8b21b6
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Pairing smul left
-- statement:
--   The actual convergent pairing is conjugate linear in its first argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L505-L511
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L505-L511

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_smul_left (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : ℂ) : lpsCuspPeterssonPairing N (c • f) g=conj c*lpsCuspPeterssonPairing N f g := by sorry
