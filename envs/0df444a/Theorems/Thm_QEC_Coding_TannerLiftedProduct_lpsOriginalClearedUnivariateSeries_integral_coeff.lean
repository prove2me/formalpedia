-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedUnivariateSeries_integral_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateSeries_integral_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:14:24.323555+00:00
-- url     : https://prove2.me/theorems/5dfcd8ba-4f6f-48b1-be5e-bacf72b2f5d4
-- title:
--   Tanner Lifted Product: lps Original Cleared Univariate Series integral coeff
-- statement:
--   Descending triangular coefficient recovery proves polynomial coefficients integral from the actual cleared series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L549-L602
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L549-L602

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedUnivariateSeries_integral_coeff
    (N D : ℕ) (hN : 0<N) (K : PowerSeries ℂ) (p : Polynomial ℂ)
    (hd : p.natDegree≤D) (hK0 : K.constantCoeff=1)
    (hK : ∀ n, IsIntegral ℤ (K.coeff n))
    (hc : ∀ n, IsIntegral ℤ
      ((lpsOriginalClearedUnivariateSeries N D K p).coeff n)) :
    ∀ n, IsIntegral ℤ (p.coeff n) := by sorry
