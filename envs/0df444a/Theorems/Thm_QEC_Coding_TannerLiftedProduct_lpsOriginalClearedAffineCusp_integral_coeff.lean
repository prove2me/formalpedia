-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_integral_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedAffineCusp_integral_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:14:03.169715+00:00
-- url     : https://prove2.me/theorems/470ca50d-5522-451c-af08-e2e8886bb4ce
-- title:
--   Tanner Lifted Product: lps Original Cleared Affine Cusp integral coeff
-- statement:
--   Every actual cleared affine cusp Taylor coefficient is an algebraic integer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L492-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L492-L502

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedAffineCusp_integral_coeff
    (B m : ℕ) (hm : m≠0) (r : ℚ) (n : ℕ) :
    IsIntegral ℤ ((lpsOriginalTaylorSeries
      (lpsOriginalClearedAffineCusp B m r)).coeff n) := by sorry
