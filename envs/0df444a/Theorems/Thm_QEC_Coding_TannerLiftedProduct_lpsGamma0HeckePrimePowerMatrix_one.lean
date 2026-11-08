-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0HeckePrimePowerMatrix_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:53:12.994145+00:00
-- url     : https://prove2.me/theorems/d01e4e52-ff01-4c72-8f0b-ff81705a2d9c
-- title:
--   Tanner Lifted Product: lps Gamma0 Hecke Prime Power Matrix one
-- statement:
--   The first prime-power Hecke matrix is the matrix of the genuine Hecke operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L141-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L141-L143

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_one (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : lpsGamma0HeckePrimePowerMatrix N p hNp 1 =
      lpsGamma0HeckeMatrix N p hNp := by sorry
