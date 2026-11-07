-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_formula
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:55:25.912523+00:00
-- url     : https://prove2.me/theorems/f268e10c-b90a-49f8-bd97-c3f9e06a3c4a
-- title:
--   Tanner Lifted Product: lps Original Filled JReciprocal cusp formula
-- statement:
--   Actual cusp-width q formula for the reciprocal, with the genuine numerator q^m.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L59-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L59-L78

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_formula (N : ℕ) [NeZero N] (a : ℂ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (q : (lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).target)
    (hq0 : q.val≠0) :
    lpsOriginalFilledJReciprocal N a (lpsOriginalFilledCuspParam N c q)=
      q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))/
      (lpsOriginalJQCoefficient (q.val^(lpsOriginalCuspWidthNat N
        (lpsOriginalCuspRepresentative N c)))-
        a*q.val^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by sorry
