-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateTerm_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateTerm_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:14:36.298097+00:00
-- url     : https://prove2.me/theorems/67479158-e43c-4c97-848c-262f24fa34ce
-- title:
--   Tanner Lifted Product: lps Original Cleared Univariate Term coeff
-- statement:
--   Exact coefficient formula for each actual cusp-clearing summand.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L542-L546
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L542-L546

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateTerm_coeff
    (N D : ℕ) (K : PowerSeries ℂ) (p : Polynomial ℂ) (i t : ℕ) :
    (PowerSeries.C (p.coeff i)*PowerSeries.X^(N*(D-i))*K^i).coeff t =
      p.coeff i * if N*(D-i)≤t then (K^i).coeff (t-N*(D-i)) else 0 := by sorry
