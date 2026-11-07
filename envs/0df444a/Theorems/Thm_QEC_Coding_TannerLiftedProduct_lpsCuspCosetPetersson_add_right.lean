-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_add_right
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:06.11726+00:00
-- url     : https://prove2.me/theorems/a0a45b88-7a43-43db-ba60-2bc80a73144b
-- title:
--   Tanner Lifted Product: lps Cusp Coset Petersson add right
-- statement:
--   The actual coset integrand is additive in its second cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L332-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L332-L338

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_add_right (N : ℕ)
    (f g h : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N f (g+h) τ γ=
      lpsCuspCosetPetersson N f g τ γ+lpsCuspCosetPetersson N f h τ γ := by sorry
