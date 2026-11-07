-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_interior_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_interior_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:00:49.269562+00:00
-- url     : https://prove2.me/theorems/135ae331-e575-4c4c-a67b-86b8eb85d270
-- title:
--   Tanner Lifted Product: lps Original Filled JReciprocal interior analytic
-- statement:
--   Actual interior chart analyticity of the reciprocal under the temporary omitted-value hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L115-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L115-L131

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_interior_analytic (N : ℕ) [NeZero N]
    (hN : 4∣N) (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by sorry
