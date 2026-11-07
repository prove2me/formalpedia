-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:07:26.082833+00:00
-- url     : https://prove2.me/theorems/261dfec4-ee23-410d-b020-6256e50c09d3
-- title:
--   Tanner Lifted Product: lps Original Cleared Cusp pullback
-- statement:
--   Actual original polynomial nome pullback after the genuine common clearing bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L439-L454
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L439-L454

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_pullback (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ)) (τ : ℍ) :
    lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P
      (Function.Periodic.qParam 1 (τ:ℂ))=
      (Function.Periodic.qParam 1 (τ:ℂ))^(lpsOriginalClearingBound N P)*
        P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (lpsOriginalJDilated N hN τ) := by sorry
