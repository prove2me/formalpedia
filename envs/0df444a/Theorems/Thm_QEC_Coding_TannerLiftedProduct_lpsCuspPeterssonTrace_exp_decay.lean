-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_exp_decay
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_exp_decay
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T09:21:56.765448+00:00
-- url     : https://prove2.me/theorems/8d89a024-6dfe-449e-a0f3-cf23a8f58daf
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Trace exp decay
-- statement:
--   The finite actual coset trace decays exponentially with a common positive exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L263-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L263-L288

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_exp_decay (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃a>0,lpsCuspPeterssonTrace N f g=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by sorry
