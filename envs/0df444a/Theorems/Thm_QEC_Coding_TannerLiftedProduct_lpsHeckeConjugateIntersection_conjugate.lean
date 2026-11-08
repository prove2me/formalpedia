-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeConjugateIntersection_conjugate
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:24.082736+00:00
-- url     : https://prove2.me/theorems/2f81424b-41fb-466e-86e5-086b745d32b2
-- title:
--   Tanner Lifted Product: lps Hecke Conjugate Intersection conjugate
-- statement:
--   Every true upper-right intersection matrix is the actual conjugate of a Gamma0(Np) matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L170-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L170-L201

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeConjugateIntersection_conjugate (N p : ℕ) [Fact p.Prime]
    (δ : SL(2,ℤ)) (hδ : δ ∈ lpsHeckeConjugateIntersection N p) :
    ∃γ : SL(2,ℤ),γ ∈ CongruenceSubgroup.Gamma0 (N*p) ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by sorry
