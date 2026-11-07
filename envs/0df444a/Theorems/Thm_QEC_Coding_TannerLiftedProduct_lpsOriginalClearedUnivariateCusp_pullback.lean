-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateCusp_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateCusp_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:15:36.366684+00:00
-- url     : https://prove2.me/theorems/cfa6b08c-ee7b-40fe-a0b0-5534abbb5ee3
-- title:
--   Tanner Lifted Product: lps Original Cleared Univariate Cusp pullback
-- statement:
--   True nome pullback evaluates the SAME polynomial at the original dilated j function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L739-L755
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L739-L755

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateCusp_pullback
    (N D : ℕ) (hN : 0<N) (p : Polynomial ℂ) (hd : p.natDegree≤D) (σ : ℍ) :
    lpsOriginalClearedUnivariateCusp N D p
        (Function.Periodic.qParam 1 (σ:ℂ))=
      Function.Periodic.qParam 1 (σ:ℂ)^(N*D) *
        p.eval (lpsOriginalJDilated N hN σ) := by sorry
