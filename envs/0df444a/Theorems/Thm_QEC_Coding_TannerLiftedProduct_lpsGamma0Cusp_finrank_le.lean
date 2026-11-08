-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Cusp_finrank_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Cusp_finrank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:52:00.294312+00:00
-- url     : https://prove2.me/theorems/5d4ecc17-5e3a-44b8-b4a8-05b3275bd6cb
-- title:
--   Tanner Lifted Product: lps Gamma0 Cusp finrank le
-- statement:
--   The genuine cusp inclusion and finite coefficient injection bound the cusp-space dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L74-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L74-L79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Cusp_finrank_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) ≤
      lpsGamma0CoefficientCount N k := by sorry
