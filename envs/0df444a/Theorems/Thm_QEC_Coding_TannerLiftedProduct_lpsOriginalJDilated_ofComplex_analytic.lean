-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_ofComplex_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilated_ofComplex_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:11.901751+00:00
-- url     : https://prove2.me/theorems/ed4ef3f8-5ccd-4f54-9775-710097358937
-- title:
--   Tanner Lifted Product: lps Original JDilated of Complex analytic
-- statement:
--   Analyticity of j(Ntau) composed with ofComplex on the actual open upper half plane; used by all actual interior targets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L333-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L333-L340

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilated_ofComplex_analytic (N : ℕ) (hpos : 0<N) (τ : ℍ) :
    AnalyticAt ℂ ((lpsOriginalJDilated N hpos)∘UpperHalfPlane.ofComplex) (τ:ℂ) := by sorry
