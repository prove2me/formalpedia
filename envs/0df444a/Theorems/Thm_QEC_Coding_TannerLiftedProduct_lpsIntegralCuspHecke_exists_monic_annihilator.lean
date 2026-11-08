-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspHecke_exists_monic_annihilator
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegralCuspHecke_exists_monic_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:36:25.550799+00:00
-- url     : https://prove2.me/theorems/3b4a5ff4-d857-4337-9ad8-dc15d01d7439
-- title:
--   Tanner Lifted Product: lps Integral Cusp Hecke exists monic annihilator
-- statement:
--   A derived monic integer polynomial annihilates the actual restricted original Hecke operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L115-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspIntegralHecke.lean#L115-L119

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

theorem QEC.Coding.TannerLiftedProduct.lpsIntegralCuspHecke_exists_monic_annihilator (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    ∃ P : ℤ[X], P.Monic ∧ aeval (lpsIntegralCuspHecke N p hNp) P = 0 := by sorry
