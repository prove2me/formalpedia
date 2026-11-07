-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero_iff_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_zero_iff_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:56:15.781451+00:00
-- url     : https://prove2.me/theorems/60b16628-cf3f-426e-b88f-aa482c9c6825
-- title:
--   Tanner Lifted Product: lps Original Taylor Series zero iff germ
-- statement:
--   Genuine equivalence between zero Taylor series and ordinary analytic zero neighborhood germ.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L180-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L180-L201

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_zero_iff_germ {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0) :
    lpsOriginalTaylorSeries f=0 ↔ f=ᶠ[𝓝 0]0 := by sorry
