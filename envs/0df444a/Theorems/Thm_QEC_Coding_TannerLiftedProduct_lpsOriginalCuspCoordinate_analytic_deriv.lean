-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_analytic_deriv
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_analytic_deriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:43:14.090622+00:00
-- url     : https://prove2.me/theorems/c8681cc7-3137-462c-ae42-dec97fc94362
-- title:
--   Tanner Lifted Product: lps Original Cusp Coordinate analytic deriv
-- statement:
--   The actual original minimal-width cusp coordinate is locally analytic with a proved nonzero derivative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean#L105-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean#L105-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_analytic_deriv (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    let f : ℂ → ℂ := fun z => lpsOriginalFilledCuspPartialEquiv N ρ
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))
    AnalyticAt ℂ f (τ:ℂ) ∧ deriv f (τ:ℂ)≠0 := by sorry
