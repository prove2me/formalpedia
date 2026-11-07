-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeIntersection_conjugate
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:07.750215+00:00
-- url     : https://prove2.me/theorems/2598d709-0770-411f-a08e-ffd8dd1346ea
-- title:
--   Tanner Lifted Product: lps Hecke Intersection conjugate
-- statement:
--   The integral dilation conjugate gives the exact equality of the original real GL products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L39-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean#L39-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeIntersection_conjugate (N p : ℕ) [Fact p.Prime]
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N*p)) :
    ∃δ : SL(2,ℤ),δ ∈ CongruenceSubgroup.Gamma0 N ∧
      lpsHeckeUpperGL ℝ p none * Matrix.SpecialLinearGroup.mapGL ℝ γ =
        Matrix.SpecialLinearGroup.mapGL ℝ δ * lpsHeckeUpperGL ℝ p none := by sorry
