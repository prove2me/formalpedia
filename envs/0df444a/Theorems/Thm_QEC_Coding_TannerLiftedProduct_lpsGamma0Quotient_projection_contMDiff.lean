-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Quotient_projection_contMDiff
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Quotient_projection_contMDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:51:17.429024+00:00
-- url     : https://prove2.me/theorems/230268f1-189b-493c-af45-6d2b5c2e6092
-- title:
--   Tanner Lifted Product: lps Gamma0 Quotient projection cont MDiff
-- statement:
--   The ORIGINAL orbit projection is complex-analytic in the proved quotient atlas.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L237-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0Quotient.lean#L237-L267

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

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Quotient_projection_contMDiff (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsGamma0QuotientChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)) := by sorry
