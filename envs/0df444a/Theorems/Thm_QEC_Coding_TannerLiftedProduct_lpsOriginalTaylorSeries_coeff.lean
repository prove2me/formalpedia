-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:27.179017+00:00
-- url     : https://prove2.me/theorems/49f8a261-4e29-4969-a959-698c3d8916ce
-- title:
--   Tanner Lifted Product: lps Original Taylor Series coeff
-- statement:
--   Literal Taylor coefficient identity from the actual PowerSeries.mk construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L38-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalQExpansionArithmetic.lean#L38-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Inverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology UpperHalfPlane ModularForm MatrixGroups
open scoped UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_coeff (f : ℂ→ℂ) (n : ℕ) :
    (lpsOriginalTaylorSeries f).coeff n=(n.factorial:ℂ)⁻¹*iteratedDeriv n f 0 := by sorry
