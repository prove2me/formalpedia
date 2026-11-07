-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateCusp_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateCusp_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:16:42.743286+00:00
-- url     : https://prove2.me/theorems/d1ce511f-4665-4ef1-a178-8fd0161f5761
-- title:
--   Tanner Lifted Product: lps Original Cleared Univariate Cusp analytic
-- statement:
--   Analyticity of the actual polynomial cusp-clearing function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L703-L710
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L703-L710

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateCusp_analytic
    (N D : ℕ) (hN : N≠0) (p : Polynomial ℂ) :
    AnalyticAt ℂ (lpsOriginalClearedUnivariateCusp N D p) 0 := by sorry
