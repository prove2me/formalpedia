-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_invariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:21:05.594552+00:00
-- url     : https://prove2.me/theorems/91224688-1a77-45f8-b71a-97dc8344b490
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Trace invariant
-- statement:
--   The actual coset trace is invariant under the whole modular group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L82-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L82-L89

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_invariant (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsCuspPeterssonTrace N f g (h • τ)=lpsCuspPeterssonTrace N f g τ := by sorry
