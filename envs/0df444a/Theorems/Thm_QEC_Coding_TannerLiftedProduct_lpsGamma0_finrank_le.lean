-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_finrank_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0_finrank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:49:57.714866+00:00
-- url     : https://prove2.me/theorems/c98a77a9-4cef-4780-962e-9cdb52d0472a
-- title:
--   Tanner Lifted Product: lps Gamma0 finrank le
-- statement:
--   The finite Fourier coefficient injection bounds the actual modular-form dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L68-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceFiniteDimension.lean#L68-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0_finrank_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) ≤
      lpsGamma0CoefficientCount N k := by sorry
