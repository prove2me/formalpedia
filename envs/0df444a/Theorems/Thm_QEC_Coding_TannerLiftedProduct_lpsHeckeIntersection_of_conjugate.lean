-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_of_conjugate
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_of_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:13:29.003713+00:00
-- url     : https://prove2.me/theorems/c474b635-694d-482a-9b18-7016580dfd1d
-- title:
--   Tanner Lifted Product: lps Hecke Intersection of conjugate
-- statement:
--   The true real GL conjugacy forces original lower-left Np divisibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L48-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L48-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_of_conjugate (N p : ℕ) [Fact p.Prime]
    (γ δ : SL(2,ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 N)
    (he : lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none) :
    γ ∈ CongruenceSubgroup.Gamma0 (N*p) := by sorry
