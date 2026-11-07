-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonTrace_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:20:48.672836+00:00
-- url     : https://prove2.me/theorems/85009e00-cc55-4084-82b5-baa0155f2553
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Trace integrable
-- statement:
--   The actual finite-coset Petersson trace has an absolutely convergent integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L109-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonTrace.lean#L109-L116

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Mathlib.Data.Finset.Lattice.Fold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonTrace_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (lpsCuspPeterssonTrace N f g) ModularGroup.fd := by sorry
