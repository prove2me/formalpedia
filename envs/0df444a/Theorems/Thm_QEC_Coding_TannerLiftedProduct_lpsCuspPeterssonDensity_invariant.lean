-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_invariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:21:14.776416+00:00
-- url     : https://prove2.me/theorems/0eb13c66-190b-4c2d-bae0-33a0499aa093
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Density invariant
-- statement:
--   The actual square density is invariant under the whole modular group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L203-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L203-L207

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_invariant (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsCuspPeterssonDensity N f (h • τ)=lpsCuspPeterssonDensity N f τ := by sorry
