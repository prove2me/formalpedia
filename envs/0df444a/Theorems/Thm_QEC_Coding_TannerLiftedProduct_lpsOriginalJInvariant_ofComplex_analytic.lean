-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_ofComplex_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_ofComplex_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:07.507239+00:00
-- url     : https://prove2.me/theorems/f513994d-0959-47b7-9791-c44305b6ecbb
-- title:
--   Tanner Lifted Product: lps Original JInvariant of Complex analytic
-- statement:
--   Complex analyticity of genuine j composed with ofComplex in the actual open half plane; used by all interior targets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L302-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L302-L309

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_ofComplex_analytic (τ : ℍ) :
    AnalyticAt ℂ (lpsOriginalJInvariant∘UpperHalfPlane.ofComplex) (τ:ℂ) := by sorry
