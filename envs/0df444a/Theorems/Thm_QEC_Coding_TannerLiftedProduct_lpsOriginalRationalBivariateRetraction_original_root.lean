-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_original_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_original_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:12:24.257978+00:00
-- url     : https://prove2.me/theorems/d28d0c32-e097-4246-b9b8-fc4f4df60d5c
-- title:
--   Tanner Lifted Product: lps Original Rational Bivariate Retraction original root
-- statement:
--   The rational transferred polynomial vanishes globally on SAME original j and jN by the true analytic identity theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L552-L593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L552-L593

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_original_root
    (N : ℕ) (hN : 0<N) (P : Polynomial (Polynomial ℂ))
    (hroot : ∀ τ : ℍ,P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
      (lpsOriginalJDilated N hN τ)=0) : ∀ τ : ℍ,
      (lpsOriginalRationalBivariateRetraction P).eval₂
        ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
          (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0 := by sorry
