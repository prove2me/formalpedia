-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseKSeries_coeff_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseKSeries_coeff_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:13:26.484199+00:00
-- url     : https://prove2.me/theorems/ab2bcfee-4cb6-408d-a082-8b7a98316a05
-- title:
--   Tanner Lifted Product: lps Original Phase KSeries coeff integral
-- statement:
--   Every coefficient of the actual phase-rescaled integer j series is an algebraic integer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L416-L421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L416-L421

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseKSeries_coeff_integral (r : ℚ) (n : ℕ) :
    IsIntegral ℤ ((PowerSeries.rescale (Function.Periodic.qParam 1 (r : ℂ))
      (PowerSeries.map (algebraMap ℤ ℂ) lpsOriginalJZSeries)).coeff n) := by sorry
