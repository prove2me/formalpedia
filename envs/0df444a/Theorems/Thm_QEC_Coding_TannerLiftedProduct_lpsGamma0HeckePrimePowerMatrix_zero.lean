-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0HeckePrimePowerMatrix_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:53:45.898003+00:00
-- url     : https://prove2.me/theorems/5b26d8cc-e2b1-44c8-a25f-0be3f2449d67
-- title:
--   Tanner Lifted Product: lps Gamma0 Hecke Prime Power Matrix zero
-- statement:
--   The genuine zeroth prime-power Hecke matrix is the identity, including a zero-dimensional space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L136-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L136-L138

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_zero (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : lpsGamma0HeckePrimePowerMatrix N p hNp 0 = 1 := by sorry
