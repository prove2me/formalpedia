-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Quotient_isManifold
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Quotient_isManifold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:51:18.340041+00:00
-- url     : https://prove2.me/theorems/d45ca597-d41e-432c-8c7c-13e9bc896fbc
-- title:
--   Tanner Lifted Product: lps Gamma0 Quotient is Manifold
-- statement:
--   The original noncompact Gamma0 orbit quotient has genuine complex-analytic transition charts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L196-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L196-L234

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Stabilizers
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Mathlib.Geometry.Manifold.Instances.Quotient
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Matrix Filter Topology
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Quotient_isManifold (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsGamma0QuotientChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) := by sorry
