-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspCoordinates_cast
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegralCuspCoordinates_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:09:37.192187+00:00
-- url     : https://prove2.me/theorems/40eddbd4-d4a2-473d-af7a-b5d1f68506d1
-- title:
--   Tanner Lifted Product: lps Integral Cusp Coordinates cast
-- statement:
--   The actual selected integer coordinate is exactly the original Fourier coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L63-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L63-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegralCuspCoordinates_cast (N : ℕ) (f : lpsIntegralCuspLattice N)
    (i : Fin (lpsGamma0CoefficientCount N 2)) :
    (lpsIntegralCuspCoordinates N f i : ℂ) = lpsCuspCoefficient N i.val f := by sorry
