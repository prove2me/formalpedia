-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_disk_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_disk_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:06:57.235695+00:00
-- url     : https://prove2.me/theorems/c16bb774-c5d3-4f5f-8931-812655766c06
-- title:
--   Tanner Lifted Product: lps Original Cleared Cusp disk zero
-- statement:
--   Original global complex relation implies zero on the punctured unit disk via a true upper-half-plane lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L457-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L457-L466

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_disk_zero (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) {q : ℂ} (hq : ‖q‖<1) (hq0 : q≠0) :
    lpsOriginalClearedCusp N (lpsOriginalClearingBound N P) P q=0 := by sorry
