-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:20:20.701028+00:00
-- url     : https://prove2.me/theorems/0ed6f8f8-300c-4360-8270-00fc2d0f3fac
-- title:
--   Tanner Lifted Product: lps Cusp Coset Petersson apply
-- statement:
--   Evaluation at a representative gives the actual transformed Petersson integrand.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L125-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L125-L128

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_apply (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (h : SL(2,ℤ)) :
    lpsCuspCosetPetersson N f g τ ⟦h⟧=petersson 2 f g (h⁻¹ • τ) := by sorry
