-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_exp_decay
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_exp_decay
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T09:21:53.319638+00:00
-- url     : https://prove2.me/theorems/d975bc27-c1b8-499a-9c06-eadb62ac54b7
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Density exp decay
-- statement:
--   The actual invariant square density decays exponentially at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L291-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L291-L299

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_exp_decay (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    ∃a>0,lpsCuspPeterssonDensity N f=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by sorry
