-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedMonomial_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:56:40.343217+00:00
-- url     : https://prove2.me/theorems/da5dd736-9041-44ff-baea-8a9d2951fd23
-- title:
--   Tanner Lifted Product: lps Original Cleared Monomial pullback
-- statement:
--   Actual nome pullback of every supported cleared monomial to the SAME original j and jN.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L349-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L349-L362

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedMonomial_pullback (N : ℕ) (hN : 0<N)
    (B i k : ℕ) (hB : i+N*k≤B) (τ : ℍ) :
    lpsOriginalClearedMonomial N B i k (Function.Periodic.qParam 1 (τ:ℂ))=
      (Function.Periodic.qParam 1 (τ:ℂ))^B*lpsOriginalJInvariant τ^i*
        lpsOriginalJDilated N hN τ^k := by sorry
