-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_cpow_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_cpow_integrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T11:11:33.372015+00:00
-- url     : https://prove2.me/theorems/72cb445b-6c63-4ad6-aa8c-7795de5fd33a
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Density cpow integrable
-- statement:
--   Every complex height power times the actual square density is integrable on the fundamental domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L408-L424
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L408-L424

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_cpow_integrable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) : IntegrableOn (fun τ : ℍ => (lpsCuspPeterssonDensity N f τ:ℂ)*(τ.im:ℂ)^s)
      ModularGroup.fd := by sorry
