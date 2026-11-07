-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:06:12.117205+00:00
-- url     : https://prove2.me/theorems/ebb240dc-5bac-4888-9c80-bca6a8b05432
-- title:
--   Tanner Lifted Product: lps Original Cleared Cusp taylor
-- statement:
--   Genuine Taylor series of the finite complex cleared cusp function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L399-L416
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L399-L416

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_taylor (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalTaylorSeries (lpsOriginalClearedCusp N B P)=
      ∑ k∈P.support,∑ i∈(P.coeff k).support,
        PowerSeries.C ((P.coeff k).coeff i)*
          PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormalMonomial N hN B i k) := by sorry
