-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedFormal_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedFormal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:09:11.993249+00:00
-- url     : https://prove2.me/theorems/f1458119-c056-4f8a-a191-d57eeb6fdd5a
-- title:
--   Tanner Lifted Product: lps Original Cleared Formal zero
-- statement:
--   The actual rational cleared formal series is zero by finite coefficientwise descent of the complex zero Taylor series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L490-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L490-L502

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedFormal_zero (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) :
    lpsOriginalClearedFormal N (Nat.ne_of_gt hN) (lpsOriginalClearingBound N P) P=0 := by sorry
