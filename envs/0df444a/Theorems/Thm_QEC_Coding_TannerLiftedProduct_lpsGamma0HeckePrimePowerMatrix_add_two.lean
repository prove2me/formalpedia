-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0HeckePrimePowerMatrix_add_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_add_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:52:36.140606+00:00
-- url     : https://prove2.me/theorems/5f47fce1-f4ff-4a07-8e85-bd978d087c5c
-- title:
--   Tanner Lifted Product: lps Gamma0 Hecke Prime Power Matrix add two
-- statement:
--   The actual finite Hecke matrices obey the exact prime-power recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L146-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L146-L153

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_add_two (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) : lpsGamma0HeckePrimePowerMatrix N p hNp (r+2) =
      lpsGamma0HeckePrimePowerMatrix N p hNp (r+1) * lpsGamma0HeckeMatrix N p hNp -
        (p:ℂ) • lpsGamma0HeckePrimePowerMatrix N p hNp r := by sorry
