-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralSeries_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralSeries_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:14:11.468651+00:00
-- url     : https://prove2.me/theorems/ca0c1395-92fe-4658-95cc-2535cb65eadf
-- title:
--   Tanner Lifted Product: lps Original Integral Series mul
-- statement:
--   Finite convolution preserves coefficientwise algebraic integrality of actual power series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L516-L521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L516-L521

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralSeries_mul (A B : PowerSeries ℂ)
    (hA : ∀ n, IsIntegral ℤ (A.coeff n))
    (hB : ∀ n, IsIntegral ℤ (B.coeff n)) (n : ℕ) :
    IsIntegral ℤ ((A*B).coeff n) := by sorry
