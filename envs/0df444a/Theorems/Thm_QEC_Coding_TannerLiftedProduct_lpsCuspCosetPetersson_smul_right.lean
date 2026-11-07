-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_smul_right
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_smul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:06.957594+00:00
-- url     : https://prove2.me/theorems/4ccc6fce-e107-4d8a-813b-ff4293a208b4
-- title:
--   Tanner Lifted Product: lps Cusp Coset Petersson smul right
-- statement:
--   The actual coset integrand is complex linear in its second cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L356-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L356-L362

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_smul_right (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (c : ℂ) (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N f (c • g) τ γ=c*lpsCuspCosetPetersson N f g τ γ := by sorry
