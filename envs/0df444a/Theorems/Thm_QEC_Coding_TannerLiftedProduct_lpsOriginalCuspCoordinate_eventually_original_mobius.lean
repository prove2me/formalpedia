-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_eventually_original_mobius
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_eventually_original_mobius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:46:29.081661+00:00
-- url     : https://prove2.me/theorems/324709f8-e404-4741-92c8-06223b2e16a8
-- title:
--   Tanner Lifted Product: lps Original Cusp Coordinate eventually original mobius
-- statement:
--   A genuine original Gamma0 group witness gives the local minimal-width Mobius/q formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L32-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialCoefficients.lean#L32-L93

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_eventually_original_mobius (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    ∃ g : GL (Fin 2) ℝ, g.val.det=1 ∧
      (Matrix.SpecialLinearGroup.mapGL ℝ ρ)*g∈
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ∧
      (fun z : ℂ => lpsOriginalFilledCuspPartialEquiv N ρ
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))) =ᶠ[𝓝 (τ:ℂ)]
      (fun z : ℂ => Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty
        ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) := by sorry
