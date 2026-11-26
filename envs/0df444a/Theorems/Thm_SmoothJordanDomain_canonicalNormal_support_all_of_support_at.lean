-- Prove2me | Theorems.Thm_SmoothJordanDomain_canonicalNormal_support_all_of_support_at
-- name    : SmoothJordanDomain.canonicalNormal_support_all_of_support_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:49.800803+00:00
-- url     : https://prove2.me/theorems/c3d9f490-0ba6-4286-bea4-0bbcbd1bd0a4
-- title:
--   Smooth Jordan Domain: canonical Normal support all of support at
-- statement:
--   For a smooth strictly convex Jordan trace, the canonical-normal sign at
--   one point of the open carrier cannot change along the parameter line.  It is
--   strict at the carrier point, never vanishes at any parameter, and continuity
--   then rules out a sign change by the intermediate value theorem.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L199-L239
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L199-L239

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
set_option autoImplicit false
open Complex Set
open scoped Real

theorem SmoothJordanDomain.canonicalNormal_support_all_of_support_at
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t0 : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t0) *
        (c - Omega.boundaryParam t0)).re ≤ 0) :
    ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0 := by sorry
