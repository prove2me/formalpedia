-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspLattice_finite
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegralCuspLattice_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:08:10.327508+00:00
-- url     : https://prove2.me/theorems/642ee409-51f2-4e43-bd4c-f9c36f3b76fd
-- title:
--   Tanner Lifted Product: lps Integral Cusp Lattice finite
-- statement:
--   This original all-integer cusp lattice is finite over Z, with no supplied lattice hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L81-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L81-L83

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

theorem QEC.Coding.TannerLiftedProduct.lpsIntegralCuspLattice_finite (N : ℕ) [NeZero N] :
    Module.Finite ℤ (lpsIntegralCuspLattice N) := by sorry
