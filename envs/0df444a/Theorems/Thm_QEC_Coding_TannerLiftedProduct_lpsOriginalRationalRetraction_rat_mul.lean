-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRetraction_rat_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRetraction_rat_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:58:16.58356+00:00
-- url     : https://prove2.me/theorems/71c0b2e9-1811-419f-a7d6-efd867955df6
-- title:
--   Tanner Lifted Product: lps Original Rational Retraction rat mul
-- statement:
--   Genuine rational linearity for a rational scalar times an arbitrary complex scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L57-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L57-L60

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRetraction_rat_mul (a : ℚ) (c : ℂ) :
    lpsOriginalRationalRetraction ((a:ℂ)*c)=
      a*lpsOriginalRationalRetraction c := by sorry
