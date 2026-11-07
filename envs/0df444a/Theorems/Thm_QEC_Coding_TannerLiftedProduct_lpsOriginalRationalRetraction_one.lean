-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRetraction_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRetraction_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:56.484206+00:00
-- url     : https://prove2.me/theorems/e9ccf804-a6f3-466d-88a1-29a7917604f5
-- title:
--   Tanner Lifted Product: lps Original Rational Retraction one
-- statement:
--   The chosen retraction sends actual complex one to rational one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L46-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L46-L48

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRetraction_one :
    lpsOriginalRationalRetraction 1=1 := by sorry
