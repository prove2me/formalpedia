-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedAffineCusp_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedAffineCusp_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:07:43.935593+00:00
-- url     : https://prove2.me/theorems/ab51637c-9f67-4a2c-bf0c-e1b81e18ed3a
-- title:
--   Tanner Lifted Product: lps Original Cleared Affine Cusp pullback
-- statement:
--   True nome pullback of the cleared affine function equals the original affine j branch times the pole weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L505-L512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L505-L512

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedAffineCusp_pullback
    (B m : ℕ) (hm : 0<m) (hmB : m≤B) (r : ℚ) (σ : ℍ) :
    lpsOriginalClearedAffineCusp B m r
        (Function.Periodic.qParam 1 (σ:ℂ))=
      Function.Periodic.qParam 1 (σ:ℂ)^B *
        lpsOriginalJInvariant (lpsE2AffineMatrix m hm (r:ℝ) • σ) := by sorry
