-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRetraction_rat
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRetraction_rat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:16:21.797915+00:00
-- url     : https://prove2.me/theorems/94e62635-5c95-44b9-8fd1-88a9b2a532f6
-- title:
--   Tanner Lifted Product: lps Original Rational Retraction rat
-- statement:
--   The actual retraction fixes every rational cast.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L51-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L51-L54

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRetraction_rat (a : ℚ) :
    lpsOriginalRationalRetraction (a:ℂ)=a := by sorry
