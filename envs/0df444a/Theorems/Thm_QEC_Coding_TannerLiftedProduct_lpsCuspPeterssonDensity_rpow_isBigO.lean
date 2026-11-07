-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_rpow_isBigO
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_rpow_isBigO
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T09:22:10.316406+00:00
-- url     : https://prove2.me/theorems/b8f43ad2-d028-4723-b651-43a82ec0e260
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Density rpow is Big O
-- statement:
--   Every real height power times the actual square density is bounded at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L378-L388
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L378-L388

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_rpow_isBigO (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℝ) : (fun τ => lpsCuspPeterssonDensity N f τ*τ.im^s)=O[atImInfty]
      (fun _ => (1:ℝ)) := by sorry
