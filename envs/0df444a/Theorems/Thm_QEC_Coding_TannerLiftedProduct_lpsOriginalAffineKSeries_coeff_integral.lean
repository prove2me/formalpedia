-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineKSeries_coeff_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAffineKSeries_coeff_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:08:54.913208+00:00
-- url     : https://prove2.me/theorems/e1d262ab-ee88-41dd-b2fb-2eb76d147b19
-- title:
--   Tanner Lifted Product: lps Original Affine KSeries coeff integral
-- statement:
--   Actual Taylor coefficients of the positive-power affine j numerator are algebraic integers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L424-L440
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L424-L440

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAffineKSeries_coeff_integral
    (r : ℚ) (m : ℕ) (hm : m ≠ 0) (n : ℕ) :
    IsIntegral ℤ ((lpsOriginalTaylorSeries
      (fun q : ℂ => lpsOriginalJQCoefficient
        (Function.Periodic.qParam 1 (r : ℂ)*q^m))).coeff n) := by sorry
