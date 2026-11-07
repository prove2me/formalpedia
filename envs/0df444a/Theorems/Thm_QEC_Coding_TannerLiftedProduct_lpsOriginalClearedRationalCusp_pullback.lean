-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedRationalCusp_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:09:47.428821+00:00
-- url     : https://prove2.me/theorems/bd680c0a-eeb8-4b88-93f2-89fd383f21cd
-- title:
--   Tanner Lifted Product: lps Original Cleared Rational Cusp pullback
-- statement:
--   Actual rational cleared cusp nome pullback to the transferred original j/jN equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L531-L548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L531-L548

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_pullback (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ)) (τ : ℍ) :
    lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P
      (Function.Periodic.qParam 1 (τ:ℂ))=
      (Function.Periodic.qParam 1 (τ:ℂ))^(lpsOriginalClearingBound N P)*
        (lpsOriginalRationalBivariateRetraction P).eval₂
          ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
            (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ) := by sorry
