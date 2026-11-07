-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_eq_component_squares
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_eq_component_squares
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:29.056231+00:00
-- url     : https://prove2.me/theorems/3735a05c-96d5-4740-8c9f-b3510bdc4e97
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Density eq component squares
-- statement:
--   The genuine invariant density is height squared times the actual component-square sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L478-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L478-L491

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_eq_component_squares (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) :
    lpsCuspPeterssonDensity N f τ=
      τ.im^2*lpsCuspComponentSquareSum N f τ := by sorry
