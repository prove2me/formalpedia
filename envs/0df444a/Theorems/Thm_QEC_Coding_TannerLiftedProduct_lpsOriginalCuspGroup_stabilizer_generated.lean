-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_stabilizer_generated
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_stabilizer_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:03.195947+00:00
-- url     : https://prove2.me/theorems/18460736-be18-4143-bdd1-4fe39b3ca1a9
-- title:
--   Tanner Lifted Product: lps Original Cusp Group stabilizer generated
-- statement:
--   The true cusp stabilizer consists of integer minimal-width translations up to center.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L125-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L125-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_stabilizer_generated (N : ℕ) (ρ : SL(2,ℤ))
    (g : GL (Fin 2) ℝ) (hg : g∈lpsOriginalCuspGroup N ρ)
    (hfix : g • (OnePoint.infty : OnePoint ℝ)=OnePoint.infty) :
    ∃ m : ℤ, g=Matrix.GeneralLinearGroup.upperRightHom
        (m • (lpsOriginalCuspGroup N ρ).strictWidthInfty) ∨
      g= -Matrix.GeneralLinearGroup.upperRightHom
        (m • (lpsOriginalCuspGroup N ρ).strictWidthInfty) := by sorry
