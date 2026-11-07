-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_add_right
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:06.803801+00:00
-- url     : https://prove2.me/theorems/8e17e0b7-19ec-410b-be79-a1d3fdbe2230
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Trace add right
-- statement:
--   The actual finite-coset trace is additive in its second cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L341-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L341-L345

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_add_right (N : ℕ) [NeZero N]
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : lpsCuspPeterssonTrace N f (g+h) τ=
      lpsCuspPeterssonTrace N f g τ+lpsCuspPeterssonTrace N f h τ := by sorry
