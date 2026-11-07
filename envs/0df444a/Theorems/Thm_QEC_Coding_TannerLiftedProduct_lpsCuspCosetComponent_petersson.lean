-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspCosetComponent_petersson
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_petersson
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:22:14.925368+00:00
-- url     : https://prove2.me/theorems/0897547e-c062-458c-a2f9-eb9ccb978630
-- title:
--   Tanner Lifted Product: lps Cusp Coset Component petersson
-- statement:
--   The actual coset integrand is the Petersson product of the two induced components.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L461-L467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L461-L467

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspCosetComponent_petersson (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (γ : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    lpsCuspCosetPetersson N f g τ γ=
      petersson 2 (lpsCuspCosetComponent N f γ) (lpsCuspCosetComponent N g γ) τ := by sorry
