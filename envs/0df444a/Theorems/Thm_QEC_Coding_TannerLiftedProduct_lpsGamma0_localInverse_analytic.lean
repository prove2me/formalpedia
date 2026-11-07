-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_localInverse_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0_localInverse_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:50:13.131206+00:00
-- url     : https://prove2.me/theorems/c8a87152-7ee8-4afc-8eeb-98598c21b447
-- title:
--   Tanner Lifted Product: lps Gamma0 local Inverse analytic
-- statement:
--   The chosen local inverse has genuine analytic Mobius transitions on every sheet overlap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L154-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L154-L193

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

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0_localInverse_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (σ τ : ℍ)
    (hs : Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ∈
      ((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ).source) :
    AnalyticAt ℂ (fun z : ℂ =>
      (((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ)
        (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)) : ℂ)) τ := by sorry
