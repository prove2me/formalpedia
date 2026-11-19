-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_exp_decay
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_exp_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:23:18.578473+00:00
-- url     : https://prove2.me/theorems/7643d9ec-93ca-446e-a8de-6ef5b3f3c101
-- title:
--   Tanner Lifted Product: lps Cusp Coset Petersson exp decay
-- statement:
--   Every actual coset component decays exponentially, using the translated cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L237-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L237-L260

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
open ConjAct Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_exp_decay (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    ∃a>0,(fun τ => lpsCuspCosetPetersson N f g τ γ)=O[atImInfty]
      (fun τ => Real.exp (-a*τ.im)) := by sorry
