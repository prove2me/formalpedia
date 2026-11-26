-- Prove2me | Theorems.Thm_SmoothJordanDomain_closure_support_and_carrier_strict_of_support_at_mem_carrier
-- name    : SmoothJordanDomain.closure_support_and_carrier_strict_of_support_at_mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:48.767489+00:00
-- url     : https://prove2.me/theorems/2dc1b176-5e80-5279-963f-944537c84dae
-- title:
--   Smooth Jordan Domain: closure support and carrier strict of support at mem carrier
-- statement:
--   At a regular trace point of a smooth convex Jordan domain, the canonical
--   complex normal is nonpositive on the closed carrier and strictly negative on
--   the open carrier as soon as its nonpositive sign is known at one carrier
--   point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L73-L193
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L73-L193

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
set_option autoImplicit false
open Complex Set
open scoped Real

theorem SmoothJordanDomain.closure_support_and_carrier_strict_of_support_at_mem_carrier
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    (∀ z ∈ closure Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (z - Omega.boundaryParam t)).re ≤ 0) ∧
    ∀ z ∈ Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (z - Omega.boundaryParam t)).re < 0 := by sorry
