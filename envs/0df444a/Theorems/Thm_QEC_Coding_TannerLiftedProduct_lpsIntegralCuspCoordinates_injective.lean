-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspCoordinates_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegralCuspCoordinates_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:08:11.651198+00:00
-- url     : https://prove2.me/theorems/df09c46b-27b1-4edc-9a8d-16ebccb9b88d
-- title:
--   Tanner Lifted Product: lps Integral Cusp Coordinates injective
-- statement:
--   Genuine congruence Sturm makes the integer coordinate map injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L69-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L69-L78

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

theorem QEC.Coding.TannerLiftedProduct.lpsIntegralCuspCoordinates_injective (N : ℕ) [NeZero N] :
    Function.Injective (lpsIntegralCuspCoordinates N) := by sorry
