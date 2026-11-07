-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_zero_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_zero_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:06:54.89647+00:00
-- url     : https://prove2.me/theorems/bba97fa1-205c-406d-9892-a51243ffb884
-- title:
--   Tanner Lifted Product: lps Original Cleared Cusp zero germ
-- statement:
--   Ordinary cleared cusp zero germ from the actual punctured-disk relation and continuity at zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L470-L487
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L470-L487

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_zero_germ (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) :
    lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P=ᶠ[𝓝 0]0 := by sorry
