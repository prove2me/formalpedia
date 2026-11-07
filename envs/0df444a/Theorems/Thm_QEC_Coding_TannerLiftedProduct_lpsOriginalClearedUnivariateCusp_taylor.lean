-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateCusp_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateCusp_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:15:32.623014+00:00
-- url     : https://prove2.me/theorems/48866570-e36c-4e3e-ba54-d07deb7ef3b4
-- title:
--   Tanner Lifted Product: lps Original Cleared Univariate Cusp taylor
-- statement:
--   Exact Taylor identity of the actual polynomial cusp-clearing function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L713-L736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L713-L736

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateCusp_taylor
    (N D : ℕ) (hN : N≠0) (p : Polynomial ℂ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedUnivariateCusp N D p)=
      lpsOriginalClearedUnivariateSeries N D
        (lpsOriginalTaylorSeries (fun q : ℂ=>lpsOriginalJQCoefficient (q^N))) p := by sorry
