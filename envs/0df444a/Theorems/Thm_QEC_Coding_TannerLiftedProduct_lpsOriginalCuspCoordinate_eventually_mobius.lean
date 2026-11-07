-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_eventually_mobius
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_eventually_mobius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:43:14.34772+00:00
-- url     : https://prove2.me/theorems/0a545b8c-2a3b-44bc-8174-dc8159119617
-- title:
--   Tanner Lifted Product: lps Original Cusp Coordinate eventually mobius
-- statement:
--   True cusp-source membership supplies a fixed actual original-group Mobius change giving the q-coordinate nearby.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean#L46-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean#L46-L102

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_eventually_mobius (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    ∃ g : GL (Fin 2) ℝ, g.val.det=1 ∧
      (fun z : ℂ => lpsOriginalFilledCuspPartialEquiv N ρ
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))) =ᶠ[𝓝 (τ:ℂ)]
      (fun z : ℂ => Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty
        ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) := by sorry
