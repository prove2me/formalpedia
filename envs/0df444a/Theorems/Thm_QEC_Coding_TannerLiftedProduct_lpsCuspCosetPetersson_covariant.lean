-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_covariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_covariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:21:03.002869+00:00
-- url     : https://prove2.me/theorems/eb77b36a-46a5-41b0-9de8-57e1e9d00c25
-- title:
--   Tanner Lifted Product: lps Cusp Coset Petersson covariant
-- statement:
--   Simultaneous modular action on the point and coset preserves the actual integrand.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L58-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L58-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_covariant (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (h : SL(2,ℤ)) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N f g (h • τ) (h • γ)=lpsCuspCosetPetersson N f g τ γ := by sorry
