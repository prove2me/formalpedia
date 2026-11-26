-- Prove2me | Theorems.Thm_SmoothJordanDomain_exists_oriented_point_canonicalOrientation
-- name    : SmoothJordanDomain.exists_oriented_point_canonicalOrientation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:40:54.958578+00:00
-- url     : https://prove2.me/theorems/d99b578e-1c54-4ad4-8564-466751db044b
-- title:
--   Smooth Jordan Domain: exists oriented point canonical Orientation
-- statement:
--   The canonical orientation has an interior point whose canonical normal
--   has the supporting sign at parameter zero.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L387-L426
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L387-L426

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
set_option autoImplicit false
open Complex Set
open scoped Real

theorem SmoothJordanDomain.exists_oriented_point_canonicalOrientation
    (Omega : SmoothJordanDomain) :
    ∃ c ∈ Omega.canonicalOrientation.carrier,
      ((starRingEnd ℂ)
          (-I * deriv Omega.canonicalOrientation.boundaryParam 0) *
        (c - Omega.canonicalOrientation.boundaryParam 0)).re ≤ 0 := by sorry
