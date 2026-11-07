-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_of_factor
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_of_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:14:58.803192+00:00
-- url     : https://prove2.me/theorems/bdfeda55-6e9a-452d-947a-c7adda42c3e0
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Intersection of factor
-- statement:
--   An actual real factor of the zero finite representative forces upper-right p divisibility.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L132-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L132-L145

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_of_factor (N p : ℕ) [Fact p.Prime]
    (γ δ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (he : lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩) *
        Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ δ *
        lpsHeckeUpperGL ℝ p (some ⟨0,(Fact.out:p.Prime).pos⟩)) :
    γ ∈ lpsHeckeConjugateIntersection N p := by sorry
