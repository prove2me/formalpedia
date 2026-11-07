-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_smul_right
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_smul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:09.149707+00:00
-- url     : https://prove2.me/theorems/a0f02bd2-c4bd-4e68-8227-edf5e6768f9b
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Trace smul right
-- statement:
--   The actual finite-coset trace is complex linear in its second cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L365-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L365-L368

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_smul_right (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : ℂ) (τ : ℍ) : lpsCuspPeterssonTrace N f (c • g) τ=c*lpsCuspPeterssonTrace N f g τ := by sorry
