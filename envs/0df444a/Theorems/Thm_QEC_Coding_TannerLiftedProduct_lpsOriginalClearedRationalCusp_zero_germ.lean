-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedRationalCusp_zero_germ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_zero_germ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:09:45.346435+00:00
-- url     : https://prove2.me/theorems/ca57266f-b92c-403f-bdab-1d2a4d387bfe
-- title:
--   Tanner Lifted Product: lps Original Cleared Rational Cusp zero germ
-- statement:
--   The actual rational cleared cusp function has ordinary zero germ by genuine Taylor uniqueness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L505-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L505-L513

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_zero_germ (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) :
    lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P=ᶠ[𝓝 0]0 := by sorry
