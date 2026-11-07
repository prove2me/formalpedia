-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetComponent_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:11:45.685678+00:00
-- url     : https://prove2.me/theorems/674d0095-86ab-4c8e-9da1-7788a8aba467
-- title:
--   Tanner Lifted Product: lps Cusp Coset Component apply
-- statement:
--   An actual induced component evaluates to the slash transform of its representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L446-L448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L446-L448

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_apply (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : SL(2,ℤ)) : lpsCuspCosetComponent N f ⟦h⟧=(f:ℍ→ℂ) ∣[(2:ℤ)] h⁻¹ := by sorry
