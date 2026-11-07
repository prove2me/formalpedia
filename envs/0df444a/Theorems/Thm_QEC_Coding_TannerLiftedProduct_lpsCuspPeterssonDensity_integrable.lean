-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:21:27.808494+00:00
-- url     : https://prove2.me/theorems/67415b1e-4e09-45d7-85d7-f9652b66c9a1
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Density integrable
-- statement:
--   The actual square density is integrable with the genuine hyperbolic measure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L210-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L210-L213

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonDensity_integrable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (lpsCuspPeterssonDensity N f) ModularGroup.fd := by sorry
