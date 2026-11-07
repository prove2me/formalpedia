-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_add
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:59:32.442377+00:00
-- url     : https://prove2.me/theorems/e525c900-9015-411b-a81d-2c4b3fa26d05
-- title:
--   Tanner Lifted Product: lps Original Taylor Series add
-- statement:
--   Actual Taylor addition for genuinely analytic functions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L142-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L142-L147

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_add {f g : ℂ→ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    lpsOriginalTaylorSeries (f+g)=lpsOriginalTaylorSeries f+lpsOriginalTaylorSeries g := by sorry
