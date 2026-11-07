-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedAffineCusp_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:07:55.567573+00:00
-- url     : https://prove2.me/theorems/70c1f6a6-bf6c-464d-a83f-0e5fa35ede76
-- title:
--   Tanner Lifted Product: lps Original Cleared Affine Cusp taylor
-- statement:
--   Exact Taylor identity for the actual cleared affine cusp function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L468-L489
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L468-L489

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedAffineCusp_taylor (B m : ℕ) (hm : m≠0) (r : ℚ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedAffineCusp B m r)=
      PowerSeries.C ((Function.Periodic.qParam 1 (r:ℂ))⁻¹) *
        (PowerSeries.X^(B-m)*lpsOriginalTaylorSeries
          (fun q : ℂ=>lpsOriginalJQCoefficient
            (Function.Periodic.qParam 1 (r:ℂ)*q^m))) := by sorry
