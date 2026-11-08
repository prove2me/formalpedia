-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:00.07802+00:00
-- url     : https://prove2.me/theorems/7f332de9-3303-4b43-872f-12787c701a13
-- title:
--   Tanner Lifted Product: lps Hecke Intersection iff
-- statement:
--   Original Gamma0(Np) membership is exactly the true infinity-representative conjugacy criterion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L69-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L69-L77

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_iff (N p : ℕ) [Fact p.Prime] (γ : SL(2,ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 (N*p) ↔
      ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
        lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
          Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by sorry
