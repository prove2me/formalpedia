-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_conj
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:05.201194+00:00
-- url     : https://prove2.me/theorems/d642e57b-9f7f-4230-af68-755c7e566a8b
-- title:
--   Tanner Lifted Product: lps Cusp Coset Petersson conj
-- statement:
--   The actual coset Petersson component is Hermitian.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L302-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L302-L307

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_conj (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N g f τ γ=conj (lpsCuspCosetPetersson N f g τ γ) := by sorry
