-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonMass_pos_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonMass_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:17:27.25398+00:00
-- url     : https://prove2.me/theorems/7d56a18a-149b-4fc9-ae81-46eeda2df6a7
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Mass pos iff
-- statement:
--   The actual square integral is strictly positive exactly when the cusp form is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonPositive.lean#L116-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonPositive.lean#L116-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Defs
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonMass_pos_iff (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    0<(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ) ↔ f≠0 := by sorry
