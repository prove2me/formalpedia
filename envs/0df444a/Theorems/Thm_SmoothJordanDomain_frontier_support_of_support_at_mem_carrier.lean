-- Prove2me | Theorems.Thm_SmoothJordanDomain_frontier_support_of_support_at_mem_carrier
-- name    : SmoothJordanDomain.frontier_support_of_support_at_mem_carrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:44:33.657967+00:00
-- url     : https://prove2.me/theorems/48224c6a-9a09-4d7a-9db3-1ee203d596a9
-- title:
--   Smooth Jordan Domain: frontier support of support at mem carrier
-- statement:
--   At a regular trace point of a smooth convex Jordan domain, the canonical
--   complex normal has a constant oriented sign on the frontier as soon as that
--   sign is known at one point of the open carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L244-L256
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L244-L256

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
set_option autoImplicit false
open Complex Set
open scoped Real

theorem SmoothJordanDomain.frontier_support_of_support_at_mem_carrier
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ xi ∈ frontier Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (xi - Omega.boundaryParam t)).re ≤ 0 := by sorry
