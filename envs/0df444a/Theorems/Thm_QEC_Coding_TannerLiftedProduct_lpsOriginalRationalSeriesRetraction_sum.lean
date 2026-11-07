-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeriesRetraction_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:00:30.63363+00:00
-- url     : https://prove2.me/theorems/6d629af0-edb8-4fc2-ae56-6f2540d792ae
-- title:
--   Tanner Lifted Product: lps Original Rational Series Retraction sum
-- statement:
--   The actual formal coefficient retraction respects arbitrary finite sums.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L277-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L277-L286

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeriesRetraction_sum {α : Type*}
    (s : Finset α) (f : α→PowerSeries ℂ) :
    lpsOriginalRationalSeriesRetraction (∑ a∈s,f a)=
      ∑ a∈s,lpsOriginalRationalSeriesRetraction (f a) := by sorry
