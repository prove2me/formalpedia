-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_comp_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_comp_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:56:24.568921+00:00
-- url     : https://prove2.me/theorems/fc8e5009-1bb8-4503-a842-68a9c6a94dd3
-- title:
--   Tanner Lifted Product: lps Original Taylor Series comp pow
-- statement:
--   Actual analytic Taylor series under q-to-q-power composition from convergent sums and uniqueness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L90-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L90-L123

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_comp_pow {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0)
    (N : ℕ) (hN : N≠0) :
    lpsOriginalTaylorSeries (fun q => f (q^N))=
      PowerSeries.expand N hN (lpsOriginalTaylorSeries f) := by sorry
