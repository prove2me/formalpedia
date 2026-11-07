-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetPetersson_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:21:00.257818+00:00
-- url     : https://prove2.me/theorems/4adb7d08-98c1-42ec-84a8-6198fc386314
-- title:
--   Tanner Lifted Product: lps Cusp Coset Petersson continuous
-- statement:
--   Every actual coset Petersson component is continuous.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L46-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L46-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetPetersson_continuous (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Continuous (fun τ => lpsCuspCosetPetersson N f g τ γ) := by sorry
