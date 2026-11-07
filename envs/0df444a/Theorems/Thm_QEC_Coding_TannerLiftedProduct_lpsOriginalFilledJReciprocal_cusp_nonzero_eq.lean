-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_nonzero_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_nonzero_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:55:26.575095+00:00
-- url     : https://prove2.me/theorems/d2243a37-8bd0-4481-8a2b-89c932497e4d
-- title:
--   Tanner Lifted Product: lps Original Filled JReciprocal cusp nonzero eq
-- statement:
--   True nonzero cusp inverse evaluates the reciprocal of the actual original filled j.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L48-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L48-L56

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_nonzero_eq (N : ℕ) [NeZero N] (a : ℂ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    lpsOriginalFilledJReciprocal N a (lpsOriginalFilledCuspParam N c q)=
      (lpsOriginalFilledJ N (lpsOriginalFilledCuspParam N c q)-a)⁻¹ := by sorry
