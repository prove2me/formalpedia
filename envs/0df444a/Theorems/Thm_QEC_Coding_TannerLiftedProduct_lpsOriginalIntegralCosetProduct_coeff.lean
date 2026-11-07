-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegralCosetProduct_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralCosetProduct_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:14:53.701771+00:00
-- url     : https://prove2.me/theorems/ef3d08fc-a68d-4df4-a441-31bb297cea99
-- title:
--   Tanner Lifted Product: lps Original Integral Coset Product coeff
-- statement:
--   Every polynomial and Taylor coefficient of an actual finite root product is integral, via the integral closure subring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L641-L661
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L641-L661

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralCosetProduct_coeff {ι : Type*}
    (s : Finset ι) (f : ι→PowerSeries ℂ)
    (hf : ∀ i∈s, ∀ n, IsIntegral ℤ ((f i).coeff n)) (k n : ℕ) :
    IsIntegral ℤ (((∏ i∈s, (Polynomial.X-Polynomial.C (f i))).coeff k).coeff n) := by sorry
