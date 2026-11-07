-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspChange_translation
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspChange_translation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:33.508207+00:00
-- url     : https://prove2.me/theorems/b5ff4897-b92e-4487-8705-7d920bcf09a6
-- title:
--   Tanner Lifted Product: lps Original Cusp Change translation
-- statement:
--   A genuine change within one original cusp orbit is a signed integral-range translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L69-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean#L69-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspChange_translation (N : ℕ) [NeZero N] (ρ ρ' : SL(2,ℤ))
    (h : lpsOriginalCuspOrbit N ρ=lpsOriginalCuspOrbit N ρ') :
    ∃ g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      ∃ x : ℝ,
        (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹*g*Matrix.SpecialLinearGroup.mapGL ℝ ρ'=
          Matrix.GeneralLinearGroup.upperRightHom x ∨
        (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹*g*Matrix.SpecialLinearGroup.mapGL ℝ ρ'=
          -Matrix.GeneralLinearGroup.upperRightHom x := by sorry
